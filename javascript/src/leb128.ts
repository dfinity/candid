// tslint:disable:no-bitwise
// Note: this file uses buffer-pipe, which on Node only, uses the Node Buffer
//       implementation, which isn't compatible with the NPM buffer package
//       which we use everywhere else. This means that we have to transform
//       one into the other, hence why every function that returns a Buffer
//       actually return `new Buffer(pipe.buffer)`.
// TODO: The best solution would be to have our own buffer type around
//       Uint8Array which is standard.
import BigNumber from 'bignumber.js';
import Pipe = require('buffer-pipe');
import { Buffer } from 'buffer/';

export function safeRead(pipe: Pipe, num: number): Buffer {
  if (pipe.buffer.length < num) {
    throw new Error('unexpected end of buffer');
  }
  return pipe.read(num);
}

export function lebEncode(value: number | BigNumber): Buffer {
  if (typeof value === 'number') {
    value = new BigNumber(value);
  }
  value = value.integerValue();
  if (value.lt(0)) {
    throw new Error('Cannot leb encode negative values.');
  }

  const pipe = new Pipe();
  while (true) {
    const i = value.mod(0x80).toNumber();
    value = value.idiv(0x80);
    if (value.eq(0)) {
      pipe.write([i]);
      break;
    } else {
      pipe.write([i | 0x80]);
    }
  }

  return new Buffer(pipe.buffer);
}

export function lebDecode(pipe: Pipe): BigNumber {
  let shift = 0;
  let value = new BigNumber(0);
  let byte;

  do {
    byte = safeRead(pipe, 1)[0];
    value = value.plus(new BigNumber(byte & 0x7f).multipliedBy(new BigNumber(2).pow(shift)));
    shift += 7;
  } while (byte >= 0x80);

  return value;
}

export function slebEncode(value: BigNumber | number): Buffer {
  if (typeof value === 'number') {
    value = new BigNumber(value);
  }
  value = value.integerValue();

  const isNeg = value.lt(0);
  if (isNeg) {
    value = value.abs().minus(1);
  }
  const pipe = new Pipe();
  while (true) {
    const i = getLowerBytes(value);
    value = value.idiv(0x80);
    if ((isNeg && value.eq(0) && (i & 0x40) !== 0) || (!isNeg && value.eq(0) && (i & 0x40) === 0)) {
      pipe.write([i]);
      break;
    } else {
      pipe.write([i | 0x80]);
    }
  }

  function getLowerBytes(num: BigNumber): number {
    const bytes = num.mod(0x80).toNumber();
    if (isNeg) {
      // We swap the bits here again, and remove 1 to do two's complement.
      return 0x80 - bytes - 1;
    } else {
      return bytes;
    }
  }
  return new Buffer(pipe.buffer);
}

export function slebDecode(pipe: Pipe): BigNumber {
  // Get the size of the buffer, then cut a buffer of that size.
  const pipeView = new Uint8Array(pipe.buffer);
  let len = 0;
  for (; len < pipeView.byteLength; len++) {
    if (pipeView[len] < 0x80) {
      // If it's a positive number, we reuse lebDecode.
      if ((pipeView[len] & 0x40) === 0) {
        return lebDecode(pipe);
      }
      break;
    }
  }

  const bytes = new Uint8Array(safeRead(pipe, len + 1));
  let value = new BigNumber(0);
  for (let i = bytes.byteLength - 1; i >= 0; i--) {
    value = value.times(0x80).plus(0x80 - (bytes[i] & 0x7f) - 1);
  }
  return value.negated().minus(1);
}

export function writeUIntLE(value: BigNumber | number, byteLength: number): Buffer {
  if ((value instanceof BigNumber && value.isNegative()) || value < 0) {
    throw new Error('Cannot write negative values.');
  }
  return writeIntLE(value, byteLength);
}

export function writeIntLE(value: BigNumber | number, byteLength: number): Buffer {
  if (typeof value === 'number') {
    value = new BigNumber(value);
  }
  value = value.integerValue();
  const pipe = new Pipe();
  let i = 0;
  let mul = new BigNumber(256);
  let sub = 0;
  let byte = value.mod(mul).toNumber();
  pipe.write([byte]);
  while (++i < byteLength) {
    if (value.lt(0) && sub === 0 && byte !== 0) {
      sub = 1;
    }
    byte = value.idiv(mul).minus(sub).mod(256).toNumber();
    pipe.write([byte]);
    mul = mul.times(256);
  }
  return new Buffer(pipe.buffer);
}

export function readUIntLE(pipe: Pipe, byteLength: number): BigNumber {
  let val = new BigNumber(safeRead(pipe, 1)[0]);
  let mul = new BigNumber(1);
  let i = 0;
  while (++i < byteLength) {
    mul = mul.times(256);
    const byte = safeRead(pipe, 1)[0];
    val = val.plus(mul.times(byte));
  }
  return val;
}

export function readIntLE(pipe: Pipe, byteLength: number): BigNumber {
  let val = readUIntLE(pipe, byteLength);
  const mul = new BigNumber(2).pow(8 * (byteLength - 1) + 7);
  if (val.gte(mul)) {
    val = val.minus(mul.times(2));
  }
  return val;
}
