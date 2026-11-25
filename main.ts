import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Exit codes: 0 halt, 2 stack underflow, 3 stack overflow, 4 div/mod by zero,
// 5 unknown opcode, 6 memory address out of range, 7 call-depth overflow,
// 8 RET with empty call stack, 9 pc out of bounds / truncated immediate,
// 10 step limit (1,000,000), 11 output limit (65,536 bytes).

// Opcode table: [byte, immediate bytes, pops, pushes].
const IMM = new Uint8Array(256);
const NEED = new Uint8Array(256);
const GIVE = new Uint8Array(256);
const KNOWN = new Uint8Array(256);
for (const [o, i, p, q] of [
  [0,0,0,0],[1,1,0,1],[2,4,0,1],[3,0,1,0],[4,0,1,2],
  [5,0,2,2],[6,0,2,3],[7,0,3,3],
  [16,0,2,1],[17,0,2,1],[18,0,2,1],[19,0,2,1],[20,0,2,1],
  [21,0,2,1],[22,0,2,1],[23,0,1,1],[24,0,2,1],[25,0,2,1],
  [26,0,2,1],[27,0,1,1],[28,0,2,1],[29,0,2,1],[30,0,2,1],
  [32,0,2,1],[33,0,2,1],[34,0,2,1],
  [48,2,0,0],[49,2,1,0],[50,2,1,0],[51,2,0,0],[52,0,0,0],
  [64,0,1,1],[65,0,2,0],[80,0,1,0],[81,0,1,0],[82,0,0,1],
  [83,0,1,0],
]) { IMM[o] = i; NEED[o] = p; GIVE[o] = q; KNOWN[o] = 1; }

function run(prog: Uint8Array, inp: Uint8Array) {
  const n = prog.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, steps = 0;
  const done = (c: number) => ({ out: out.slice(0, ol), code: c });
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = prog[pc];
    if (!KNOWN[op]) return done(5);
    const imm = IMM[op];
    if (pc + imm >= n) return done(9);
    steps++;
    const nx = pc + 1 + imm;
    const pops = NEED[op], pushes = GIVE[op];
    if (sp < pops) return done(2);
    if (sp - pops + pushes > 256) return done(3);
    pc = nx;
    switch (op) {
      case 0: return done(0);
      case 1: D[sp++] = (prog[nx - 1] << 24) >> 24; break;
      case 2: D[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24); break;
      case 3: sp--; break;
      case 4: D[sp++] = D[sp - 2]; break;
      case 5: [D[sp - 1], D[sp - 2]] = [D[sp - 2], D[sp - 1]]; break;
      case 6: D[sp] = D[sp - 2]; sp++; break;
      case 7: [D[sp - 3], D[sp - 2], D[sp - 1]] = [D[sp - 2], D[sp - 1], D[sp - 3]]; break;
      case 23: D[sp - 1] = -D[sp - 1] | 0; break;
      case 27: D[sp - 1] = ~D[sp - 1]; break;
      case 48: { const r = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16; pc = nx + r; break; }
      case 49: { const r = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16; if (D[--sp] === 0) pc = nx + r; break; }
      case 50: { const r = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16; if (D[--sp] !== 0) pc = nx + r; break; }
      case 51: if (cp === 64) return done(7); C[cp++] = nx; pc = prog[nx - 2] | (prog[nx - 1] << 8); break;
      case 52: if (cp === 0) return done(8); pc = C[--cp]; break;
      case 64: { const a = D[sp - 1]; if (a < 0 || a >= 256) return done(6); D[sp - 1] = M[a]; break; }
      case 65: { const a = D[sp - 1], v = D[sp - 2]; if (a < 0 || a >= 256) return done(6); sp -= 2; M[a] = v; break; }
      case 80: { const b = Buffer.from(String(D[sp - 1])); if (ol + b.length > 65536) return done(11); sp--; out.set(b, ol); ol += b.length; break; }
      case 81: if (ol + 1 > 65536) return done(11); out[ol++] = D[--sp] & 255; break;
      case 82: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 83: return done(D[--sp] & 255);
      default: {
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) { if (b === 0) return done(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 20) { if (b === 0) return done(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 21) { if (b === 0) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 22) { if (b === 0) return done(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR || '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR || '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
