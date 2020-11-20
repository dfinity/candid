// tslint:disable:max-classes-per-file
import BigNumber from 'bignumber.js';
import Pipe = require('buffer-pipe');
import { Buffer } from 'buffer/';
import { Principal as PrincipalId } from './principal';
import { JsonValue } from './types';
import { idlLabelToId } from './utils/hash';
import { lebDecode, lebEncode, safeRead, slebDecode, slebEncode } from './utils/leb128';
import { readIntLE, readUIntLE, writeIntLE, writeUIntLE } from './utils/leb128';

// tslint:disable:max-line-length
/**
 * This module provides a combinator library to create serializers/deserializers
 * between JavaScript values and IDL used by canisters on the Internet Computer,
 * as documented at https://github.com/dfinity/candid/blob/119703ba342d2fef6ab4972d2541b9fe36ae8e36/spec/Candid.md
 */
// tslint:enable:max-line-length

const enum IDLTypeIds {
  Null = -1,
  Bool = -2,
  Nat = -3,
  Int = -4,
  Float32 = -13,
  Float64 = -14,
  Text = -15,
  Reserved = -16,
  Empty = -17,
  Opt = -18,
  Vector = -19,
  Record = -20,
  Variant = -21,
  Func = -22,
  Service = -23,
  Principal = -24,
}

const magicNumber = 'DIDL';

function zipWith<TX, TY, TR>(xs: TX[], ys: TY[], f: (a: TX, b: TY) => TR): TR[] {
  return xs.map((x, i) => f(x, ys[i]));
}

/**
 * An IDL Type Table, which precedes the data in the stream.
 */
class TypeTable {
  // List of types. Needs to be an array as the index needs to be stable.
  private _typs: Buffer[] = [];
  private _idx = new Map<string, number>();

  public has(obj: ConstructType) {
    return this._idx.has(obj.name);
  }

  public add<T>(type: ConstructType<T>, buf: Buffer) {
    const idx = this._typs.length;
    this._idx.set(type.name, idx);
    this._typs.push(buf);
  }

  public merge<T>(obj: ConstructType<T>, knot: string) {
    const idx = this._idx.get(obj.name);
    const knotIdx = this._idx.get(knot);
    if (idx === undefined) {
      throw new Error('Missing type index for ' + obj);
    }
    if (knotIdx === undefined) {
      throw new Error('Missing type index for ' + knot);
    }
    this._typs[idx] = this._typs[knotIdx];

    // Delete the type.
    this._typs.splice(knotIdx, 1);
    this._idx.delete(knot);
  }

  public encode() {
    const len = lebEncode(this._typs.length);
    const buf = Buffer.concat(this._typs);
    return Buffer.concat([len, buf]);
  }

  public indexOf(typeName: string) {
    if (!this._idx.has(typeName)) {
      throw new Error('Missing type index for ' + typeName);
    }
    return slebEncode(this._idx.get(typeName) || 0);
  }
}

export abstract class Visitor<D, R> {
  public visitType<T>(t: Type<T>, data: D): R {
    throw new Error('Not implemented');
  }
  public visitPrimitive<T>(t: PrimitiveType<T>, data: D): R {
    return this.visitType(t, data);
  }
  public visitEmpty(t: EmptyClass, data: D): R {
    return this.visitPrimitive(t, data);
  }
  public visitBool(t: BoolClass, data: D): R {
    return this.visitPrimitive(t, data);
  }
  public visitNull(t: NullClass, data: D): R {
    return this.visitPrimitive(t, data);
  }
  public visitReserved(t: ReservedClass, data: D): R {
    return this.visitPrimitive(t, data);
  }
  public visitText(t: TextClass, data: D): R {
    return this.visitPrimitive(t, data);
  }
  public visitNumber<T>(t: PrimitiveType<T>, data: D): R {
    return this.visitPrimitive(t, data);
  }
  public visitInt(t: IntClass, data: D): R {
    return this.visitNumber(t, data);
  }
  public visitNat(t: NatClass, data: D): R {
    return this.visitNumber(t, data);
  }
  public visitFloat(t: FloatClass, data: D): R {
    return this.visitPrimitive(t, data);
  }
  public visitFixedInt(t: FixedIntClass, data: D): R {
    return this.visitNumber(t, data);
  }
  public visitFixedNat(t: FixedNatClass, data: D): R {
    return this.visitNumber(t, data);
  }
  public visitPrincipal(t: PrincipalClass, data: D): R {
    return this.visitPrimitive(t, data);
  }

  public visitConstruct<T>(t: ConstructType<T>, data: D): R {
    return this.visitType(t, data);
  }
  public visitVec<T>(t: VecClass<T>, ty: Type<T>, data: D): R {
    return this.visitConstruct(t, data);
  }
  public visitOpt<T>(t: OptClass<T>, ty: Type<T>, data: D): R {
    return this.visitConstruct(t, data);
  }
  public visitRecord(t: RecordClass, fields: Array<[string, Type]>, data: D): R {
    return this.visitConstruct(t, data);
  }
  public visitTuple<T extends any[]>(t: TupleClass<T>, components: Type[], data: D): R {
    const fields: Array<[string, Type]> = components.map((ty, i) => [`_${i}_`, ty]);
    return this.visitRecord(t, fields, data);
  }
  public visitVariant(t: VariantClass, fields: Array<[string, Type]>, data: D): R {
    return this.visitConstruct(t, data);
  }
  public visitRec<T>(t: RecClass<T>, ty: ConstructType<T>, data: D): R {
    return this.visitConstruct(ty, data);
  }
  public visitFunc(t: FuncClass, data: D): R {
    return this.visitConstruct(t, data);
  }
  public visitService(t: ServiceClass, data: D): R {
    return this.visitConstruct(t, data);
  }
}

/**
 * Represents an IDL type.
 */
export abstract class Type<T = any> {
  public abstract readonly name: string;
  public abstract accept<D, R>(v: Visitor<D, R>, d: D): R;

  /* Display type name */
  public display(): string {
    return this.name;
  }

  public valueToString(x: T): string {
    return JSON.stringify(x);
  }

  /* Implement `T` in the IDL spec, only needed for non-primitive types */
  public buildTypeTable(typeTable: TypeTable): void {
    if (!typeTable.has(this)) {
      this._buildTypeTableImpl(typeTable);
    }
  }

  /**
   * Assert that JavaScript's `x` is the proper type represented by this
   * Type.
   */
  public abstract covariant(x: any): x is T;

  /**
   * Encode the value. This needs to be public because it is used by
   * encodeValue() from different types.
   * @internal
   */
  public abstract encodeValue(x: T): Buffer;

  /**
   * Implement `I` in the IDL spec.
   * Encode this type for the type table.
   */
  public abstract encodeType(typeTable: TypeTable): Buffer;

  public abstract checkType(t: Type): Type;
  public abstract decodeValue(x: Pipe, t: Type): T;

  protected abstract _buildTypeTableImpl(typeTable: TypeTable): void;
}

export abstract class PrimitiveType<T = any> extends Type<T> {
  public checkType(t: Type): Type {
    if (this.name !== t.name) {
      throw new Error(`type mismatch: type on the wire ${t.name}, expect type ${this.name}`);
    }
    return t;
  }
  public _buildTypeTableImpl(typeTable: TypeTable): void {
    // No type table encoding for Primitive types.
    return;
  }
}

export abstract class ConstructType<T = any> extends Type<T> {
  public checkType(t: Type): ConstructType<T> {
    if (t instanceof RecClass) {
      const ty = t.getType();
      if (typeof ty === 'undefined') {
        throw new Error('type mismatch with uninitialized type');
      }
      return ty;
    }
    throw new Error(`type mismatch: type on the wire ${t.name}, expect type ${this.name}`);
  }
  public encodeType(typeTable: TypeTable) {
    return typeTable.indexOf(this.name);
  }
}

/**
 * Represents an IDL Empty, a type which has no inhabitants.
 * Since no values exist for this type, it cannot be serialised or deserialised.
 * Result types like `Result<Text, Empty>` should always succeed.
 */
export class EmptyClass extends PrimitiveType<never> {
  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitEmpty(this, d);
  }

  public covariant(x: any): x is never {
    return false;
  }

  public encodeValue(): never {
    throw new Error('Empty cannot appear as a function argument');
  }

  public valueToString(): never {
    throw new Error('Empty cannot appear as a value');
  }

  public encodeType() {
    return slebEncode(IDLTypeIds.Empty);
  }

  public decodeValue(): never {
    throw new Error('Empty cannot appear as an output');
  }

  get name() {
    return 'empty';
  }
}

/**
 * Represents an IDL Bool
 */
export class BoolClass extends PrimitiveType<boolean> {
  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitBool(this, d);
  }

  public covariant(x: any): x is boolean {
    return typeof x === 'boolean';
  }

  public encodeValue(x: boolean): Buffer {
    const buf = Buffer.alloc(1);
    buf.writeInt8(x ? 1 : 0, 0);
    return buf;
  }

  public encodeType() {
    return slebEncode(IDLTypeIds.Bool);
  }

  public decodeValue(b: Pipe, t: Type) {
    this.checkType(t);
    const x = safeRead(b, 1).toString('hex');
    if (x === '00') {
      return false;
    } else if (x === '01') {
      return true;
    } else {
      throw new Error('Boolean value out of range');
    }
  }

  get name() {
    return 'bool';
  }
}

/**
 * Represents an IDL Null
 */
export class NullClass extends PrimitiveType<null> {
  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitNull(this, d);
  }

  public covariant(x: any): x is null {
    return x === null;
  }

  public encodeValue() {
    return Buffer.alloc(0);
  }

  public encodeType() {
    return slebEncode(IDLTypeIds.Null);
  }

  public decodeValue(b: Pipe, t: Type) {
    this.checkType(t);
    return null;
  }

  get name() {
    return 'null';
  }
}

/**
 * Represents an IDL Reserved
 */
export class ReservedClass extends PrimitiveType<any> {
  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitReserved(this, d);
  }

  public covariant(x: any): x is any {
    return true;
  }

  public encodeValue() {
    return Buffer.alloc(0);
  }

  public encodeType() {
    return slebEncode(IDLTypeIds.Reserved);
  }

  public decodeValue(b: Pipe, t: Type) {
    if (t.name !== this.name) {
      t.decodeValue(b, t);
    }
    return null;
  }

  get name() {
    return 'reserved';
  }
}

function isValidUTF8(buf: Buffer): boolean {
  return Buffer.compare(new Buffer(buf.toString(), 'utf8'), buf) === 0;
}

/**
 * Represents an IDL Text
 */
export class TextClass extends PrimitiveType<string> {
  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitText(this, d);
  }

  public covariant(x: any): x is string {
    return typeof x === 'string';
  }

  public encodeValue(x: string) {
    const buf = Buffer.from(x, 'utf8');
    const len = lebEncode(buf.length);
    return Buffer.concat([len, buf]);
  }

  public encodeType() {
    return slebEncode(IDLTypeIds.Text);
  }

  public decodeValue(b: Pipe, t: Type) {
    this.checkType(t);
    const len = lebDecode(b).toNumber();
    const buf = safeRead(b, len);
    if (!isValidUTF8(buf)) {
      throw new Error('Not valid UTF8 text');
    }
    return buf.toString('utf8');
  }

  get name() {
    return 'text';
  }

  public valueToString(x: string) {
    return '"' + x + '"';
  }
}

/**
 * Represents an IDL Int
 */
export class IntClass extends PrimitiveType<BigNumber> {
  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitInt(this, d);
  }

  public covariant(x: any): x is BigNumber {
    // We allow encoding of JavaScript plain numbers.
    // But we will always decode to BigNumber.
    return (BigNumber.isBigNumber(x) && x.isInteger()) || Number.isInteger(x);
  }

  public encodeValue(x: BigNumber | number) {
    return slebEncode(x);
  }

  public encodeType() {
    return slebEncode(IDLTypeIds.Int);
  }

  public decodeValue(b: Pipe, t: Type) {
    this.checkType(t);
    return slebDecode(b);
  }

  get name() {
    return 'int';
  }

  public valueToString(x: BigNumber) {
    return x.toFixed();
  }
}

/**
 * Represents an IDL Nat
 */
export class NatClass extends PrimitiveType<BigNumber> {
  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitNat(this, d);
  }

  public covariant(x: any): x is BigNumber {
    // We allow encoding of JavaScript plain numbers.
    // But we will always decode to BigNumber.
    return (
      (BigNumber.isBigNumber(x) && x.isInteger() && !x.isNegative()) ||
      (Number.isInteger(x) && x >= 0)
    );
  }

  public encodeValue(x: BigNumber | number) {
    return lebEncode(x);
  }

  public encodeType() {
    return slebEncode(IDLTypeIds.Nat);
  }

  public decodeValue(b: Pipe, t: Type) {
    this.checkType(t);
    return lebDecode(b);
  }

  get name() {
    return 'nat';
  }

  public valueToString(x: BigNumber) {
    return x.toFixed();
  }
}

/**
 * Represents an IDL Float
 */
export class FloatClass extends PrimitiveType<number> {
  constructor(private _bits: number) {
    super();
    if (_bits !== 32 && _bits !== 64) {
      throw new Error('not a valid float type');
    }
  }
  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitFloat(this, d);
  }

  public covariant(x: any): x is number {
    return typeof x === 'number' || x instanceof Number;
  }

  public encodeValue(x: number) {
    const buf = Buffer.allocUnsafe(this._bits / 8);
    if (this._bits === 32) {
      buf.writeFloatLE(x, 0);
    } else {
      buf.writeDoubleLE(x, 0);
    }
    return buf;
  }

  public encodeType() {
    const opcode = this._bits === 32 ? IDLTypeIds.Float32 : IDLTypeIds.Float64;
    return slebEncode(opcode);
  }

  public decodeValue(b: Pipe, t: Type) {
    this.checkType(t);
    const x = safeRead(b, this._bits / 8);
    if (this._bits === 32) {
      return x.readFloatLE(0);
    } else {
      return x.readDoubleLE(0);
    }
  }

  get name() {
    return 'float' + this._bits;
  }

  public valueToString(x: number) {
    return x.toString();
  }
}

/**
 * Represents an IDL fixed-width Int(n)
 */
export class FixedIntClass extends PrimitiveType<BigNumber | number> {
  constructor(private _bits: number) {
    super();
  }

  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitFixedInt(this, d);
  }

  public covariant(x: any): x is BigNumber {
    const min = new BigNumber(2).pow(this._bits - 1).negated();
    const max = new BigNumber(2).pow(this._bits - 1).minus(1);
    if (BigNumber.isBigNumber(x) && x.isInteger()) {
      return x.gte(min) && x.lte(max);
    } else if (Number.isInteger(x)) {
      const v = new BigNumber(x);
      return v.gte(min) && v.lte(max);
    } else {
      return false;
    }
  }

  public encodeValue(x: BigNumber | number) {
    return writeIntLE(x, this._bits / 8);
  }

  public encodeType() {
    const offset = Math.log2(this._bits) - 3;
    return slebEncode(-9 - offset);
  }

  public decodeValue(b: Pipe, t: Type) {
    this.checkType(t);
    const num = readIntLE(b, this._bits / 8);
    if (this._bits <= 32) {
      return num.toNumber();
    } else {
      return num;
    }
  }

  get name() {
    return `int${this._bits}`;
  }

  public valueToString(x: BigNumber | number) {
    return x.toString();
  }
}

/**
 * Represents an IDL fixed-width Nat(n)
 */
export class FixedNatClass extends PrimitiveType<BigNumber | number> {
  constructor(private _bits: number) {
    super();
  }

  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitFixedNat(this, d);
  }

  public covariant(x: any): x is BigNumber {
    const max = new BigNumber(2).pow(this._bits);
    if (BigNumber.isBigNumber(x) && x.isInteger() && !x.isNegative()) {
      return x.lt(max);
    } else if (Number.isInteger(x) && x >= 0) {
      const v = new BigNumber(x);
      return v.lt(max);
    } else {
      return false;
    }
  }

  public encodeValue(x: BigNumber | number) {
    return writeUIntLE(x, this._bits / 8);
  }

  public encodeType() {
    const offset = Math.log2(this._bits) - 3;
    return slebEncode(-5 - offset);
  }

  public decodeValue(b: Pipe, t: Type) {
    this.checkType(t);
    const num = readUIntLE(b, this._bits / 8);
    if (this._bits <= 32) {
      return num.toNumber();
    } else {
      return num;
    }
  }

  get name() {
    return `nat${this._bits}`;
  }

  public valueToString(x: BigNumber | number) {
    return x.toString();
  }
}

/**
 * Represents an IDL Array
 * @param {Type} t
 */
export class VecClass<T> extends ConstructType<T[]> {
  constructor(protected _type: Type<T>) {
    super();
  }

  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitVec(this, this._type, d);
  }

  public covariant(x: any): x is T[] {
    return Array.isArray(x) && x.every(v => this._type.covariant(v));
  }

  public encodeValue(x: T[]) {
    const len = lebEncode(x.length);
    return Buffer.concat([len, ...x.map(d => this._type.encodeValue(d))]);
  }

  public _buildTypeTableImpl(typeTable: TypeTable) {
    this._type.buildTypeTable(typeTable);

    const opCode = slebEncode(IDLTypeIds.Vector);
    const buffer = this._type.encodeType(typeTable);
    typeTable.add(this, Buffer.concat([opCode, buffer]));
  }

  public decodeValue(b: Pipe, t: Type): any[] {
    const vec = this.checkType(t);
    if (!(vec instanceof VecClass)) {
      throw new Error('Not a vector type');
    }
    const len = lebDecode(b).toNumber();
    const rets: any[] = [];
    for (let i = 0; i < len; i++) {
      rets.push(this._type.decodeValue(b, vec._type));
    }
    return rets;
  }

  get name() {
    return `vec ${this._type.name}`;
  }

  public display() {
    return `vec ${this._type.display()}`;
  }

  public valueToString(x: T[]) {
    const elements = x.map(e => this._type.valueToString(e));
    return 'vec {' + elements.join('; ') + '}';
  }
}

/**
 * Represents an IDL Option
 * @param {Type} t
 */
export class OptClass<T> extends ConstructType<[T] | []> {
  constructor(protected _type: Type<T>) {
    super();
  }

  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitOpt(this, this._type, d);
  }

  public covariant(x: any): x is [T] | [] {
    return Array.isArray(x) && (x.length === 0 || (x.length === 1 && this._type.covariant(x[0])));
  }

  public encodeValue(x: [T] | []) {
    if (x.length === 0) {
      return Buffer.from([0]);
    } else {
      return Buffer.concat([Buffer.from([1]), this._type.encodeValue(x[0])]);
    }
  }

  public _buildTypeTableImpl(typeTable: TypeTable) {
    this._type.buildTypeTable(typeTable);

    const opCode = slebEncode(IDLTypeIds.Opt);
    const buffer = this._type.encodeType(typeTable);
    typeTable.add(this, Buffer.concat([opCode, buffer]));
  }

  public decodeValue(b: Pipe, t: Type): [T] | [] {
    const opt = this.checkType(t);
    if (!(opt instanceof OptClass)) {
      throw new Error('Not an option type');
    }
    const len = safeRead(b, 1).toString('hex');
    if (len === '00') {
      return [];
    } else if (len === '01') {
      return [this._type.decodeValue(b, opt._type)];
    } else {
      throw new Error('Not an option value');
    }
  }

  get name() {
    return `opt ${this._type.name}`;
  }

  public display() {
    return `opt ${this._type.display()}`;
  }

  public valueToString(x: [T] | []) {
    if (x.length === 0) {
      return 'null';
    } else {
      return `opt ${this._type.valueToString(x[0])}`;
    }
  }
}

/**
 * Represents an IDL Record
 * @param {Object} [fields] - mapping of function name to Type
 */
export class RecordClass extends ConstructType<Record<string, any>> {
  protected readonly _fields: Array<[string, Type]>;

  constructor(fields: Record<string, Type> = {}) {
    super();
    this._fields = Object.entries(fields).sort((a, b) => idlLabelToId(a[0]) - idlLabelToId(b[0]));
  }

  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitRecord(this, this._fields, d);
  }

  public tryAsTuple(): Type[] | null {
    const res: Type[] = [];
    for (let i = 0; i < this._fields.length; i++) {
      const [key, type] = this._fields[i];
      if (key !== `_${i}_`) {
        return null;
      }
      res.push(type);
    }
    return res;
  }

  public covariant(x: any): x is Record<string, any> {
    return (
      typeof x === 'object' &&
      this._fields.every(([k, t]) => {
        if (!x.hasOwnProperty(k)) {
          throw new Error(`Record is missing key "${k}".`);
        }
        return t.covariant(x[k]);
      })
    );
  }

  public encodeValue(x: Record<string, any>) {
    const values = this._fields.map(([key]) => x[key]);
    const bufs = zipWith(this._fields, values, ([, c], d) => c.encodeValue(d));
    return Buffer.concat(bufs);
  }

  public _buildTypeTableImpl(T: TypeTable) {
    this._fields.forEach(([_, value]) => value.buildTypeTable(T));
    const opCode = slebEncode(IDLTypeIds.Record);
    const len = lebEncode(this._fields.length);
    const fields = this._fields.map(([key, value]) =>
      Buffer.concat([lebEncode(idlLabelToId(key)), value.encodeType(T)]),
    );

    T.add(this, Buffer.concat([opCode, len, Buffer.concat(fields)]));
  }

  public decodeValue(b: Pipe, t: Type) {
    const record = this.checkType(t);
    if (!(record instanceof RecordClass)) {
      throw new Error('Not a record type');
    }
    const x: Record<string, any> = {};
    let idx = 0;
    for (const [hash, type] of record._fields) {
      if (idx >= this._fields.length || idlLabelToId(this._fields[idx][0]) !== idlLabelToId(hash)) {
        // skip field
        type.decodeValue(b, type);
        continue;
      }
      const [expectKey, expectType] = this._fields[idx];
      x[expectKey] = expectType.decodeValue(b, type);
      idx++;
    }
    if (idx < this._fields.length) {
      throw new Error('Cannot find field ' + this._fields[idx][0]);
    }
    return x;
  }

  get name() {
    const fields = this._fields.map(([key, value]) => key + ':' + value.name);
    return `record {${fields.join('; ')}}`;
  }

  public display() {
    const fields = this._fields.map(([key, value]) => key + ':' + value.display());
    return `record {${fields.join('; ')}}`;
  }

  public valueToString(x: Record<string, any>) {
    const values = this._fields.map(([key]) => x[key]);
    const fields = zipWith(this._fields, values, ([k, c], d) => k + '=' + c.valueToString(d));
    return `record {${fields.join('; ')}}`;
  }
}

/**
 * Represents Tuple, a syntactic sugar for Record.
 * @param {Type} components
 */
export class TupleClass<T extends any[]> extends RecordClass {
  protected readonly _components: Type[];

  constructor(_components: Type[]) {
    const x: Record<string, any> = {};
    _components.forEach((e, i) => (x['_' + i + '_'] = e));
    super(x);
    this._components = _components;
  }

  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitTuple(this, this._components, d);
  }

  public covariant(x: any): x is T {
    // `>=` because tuples can be covariant when encoded.
    return (
      Array.isArray(x) &&
      x.length >= this._fields.length &&
      this._components.every((t, i) => t.covariant(x[i]))
    );
  }

  public encodeValue(x: any[]) {
    const bufs = zipWith(this._components, x, (c, d) => c.encodeValue(d));
    return Buffer.concat(bufs);
  }

  public decodeValue(b: Pipe, t: Type): T {
    const tuple = this.checkType(t);
    if (!(tuple instanceof TupleClass)) {
      throw new Error('not a tuple type');
    }
    if (tuple._components.length < this._components.length) {
      throw new Error('tuple mismatch');
    }
    const res = [];
    for (const [i, wireType] of tuple._components.entries()) {
      if (i >= this._components.length) {
        // skip value
        wireType.decodeValue(b, wireType);
      } else {
        res.push(this._components[i].decodeValue(b, wireType));
      }
    }
    return res as T;
  }

  public display() {
    const fields = this._components.map(value => value.display());
    return `record {${fields.join('; ')}}`;
  }

  public valueToString(values: any[]) {
    const fields = zipWith(this._components, values, (c, d) => c.valueToString(d));
    return `record {${fields.join('; ')}}`;
  }
}

/**
 * Represents an IDL Variant
 * @param {Object} [fields] - mapping of function name to Type
 */
export class VariantClass extends ConstructType<Record<string, any>> {
  private readonly _fields: Array<[string, Type]>;

  constructor(fields: Record<string, Type> = {}) {
    super();
    this._fields = Object.entries(fields).sort((a, b) => idlLabelToId(a[0]) - idlLabelToId(b[0]));
  }

  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitVariant(this, this._fields, d);
  }

  public covariant(x: any): x is Record<string, any> {
    return (
      typeof x === 'object' &&
      Object.entries(x).length === 1 &&
      this._fields.every(([k, v]) => {
        return !x.hasOwnProperty(k) || v.covariant(x[k]);
      })
    );
  }

  public encodeValue(x: Record<string, any>) {
    for (let i = 0; i < this._fields.length; i++) {
      const [name, type] = this._fields[i];
      if (x.hasOwnProperty(name)) {
        const idx = lebEncode(i);
        const buf = type.encodeValue(x[name]);

        return Buffer.concat([idx, buf]);
      }
    }
    throw Error('Variant has no data: ' + x);
  }

  public _buildTypeTableImpl(typeTable: TypeTable) {
    this._fields.forEach(([, type]) => {
      type.buildTypeTable(typeTable);
    });
    const opCode = slebEncode(IDLTypeIds.Variant);
    const len = lebEncode(this._fields.length);
    const fields = this._fields.map(([key, value]) =>
      Buffer.concat([lebEncode(idlLabelToId(key)), value.encodeType(typeTable)]),
    );
    typeTable.add(this, Buffer.concat([opCode, len, ...fields]));
  }

  public decodeValue(b: Pipe, t: Type) {
    const variant = this.checkType(t);
    if (!(variant instanceof VariantClass)) {
      throw new Error('Not a variant type');
    }
    const idx = lebDecode(b).toNumber();
    if (idx >= variant._fields.length) {
      throw Error('Invalid variant index: ' + idx);
    }
    const [wireHash, wireType] = variant._fields[idx];
    for (const [key, expectType] of this._fields) {
      if (idlLabelToId(wireHash) === idlLabelToId(key)) {
        const value = expectType.decodeValue(b, wireType);
        return { [key]: value };
      }
    }
    throw new Error('Cannot find field hash ' + wireHash);
  }

  get name() {
    const fields = this._fields.map(([key, type]) => key + ':' + type.name);
    return `variant {${fields.join('; ')}}`;
  }

  public display() {
    const fields = this._fields.map(
      ([key, type]) => key + (type.name === 'null' ? '' : `:${type.display()}`),
    );
    return `variant {${fields.join('; ')}}`;
  }

  public valueToString(x: Record<string, any>) {
    for (const [name, type] of this._fields) {
      if (x.hasOwnProperty(name)) {
        const value = type.valueToString(x[name]);
        if (value === 'null') {
          return `variant {${name}}`;
        } else {
          return `variant {${name}=${value}}`;
        }
      }
    }
    throw new Error('Variant has no data: ' + x);
  }
}

/**
 * Represents a reference to an IDL type, used for defining recursive data
 * types.
 */
export class RecClass<T = any> extends ConstructType<T> {
  private static _counter = 0;
  private _id = RecClass._counter++;
  private _type: ConstructType<T> | undefined = undefined;

  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    if (!this._type) {
      throw Error('Recursive type uninitialized.');
    }
    return v.visitRec(this, this._type, d);
  }

  public fill(t: ConstructType<T>) {
    this._type = t;
  }

  public getType() {
    return this._type;
  }

  public covariant(x: any): x is T {
    return this._type ? this._type.covariant(x) : false;
  }

  public encodeValue(x: T) {
    if (!this._type) {
      throw Error('Recursive type uninitialized.');
    }
    return this._type.encodeValue(x);
  }

  public _buildTypeTableImpl(typeTable: TypeTable) {
    if (!this._type) {
      throw Error('Recursive type uninitialized.');
    }
    typeTable.add(this, Buffer.alloc(0));
    this._type.buildTypeTable(typeTable);
    typeTable.merge(this, this._type.name);
  }

  public decodeValue(b: Pipe, t: Type) {
    if (!this._type) {
      throw Error('Recursive type uninitialized.');
    }
    return this._type.decodeValue(b, t);
  }

  get name() {
    return `rec_${this._id}`;
  }

  public display() {
    if (!this._type) {
      throw Error('Recursive type uninitialized.');
    }
    return `μ${this.name}.${this._type.name}`;
  }

  public valueToString(x: T) {
    if (!this._type) {
      throw Error('Recursive type uninitialized.');
    }
    return this._type.valueToString(x);
  }
}

function decodePrincipalId(b: Pipe): PrincipalId {
  const x = safeRead(b, 1).toString('hex');
  if (x !== '01') {
    throw new Error('Cannot decode principal');
  }
  const len = lebDecode(b).toNumber();
  const hex = safeRead(b, len).toString('hex').toUpperCase();
  return PrincipalId.fromHex(hex);
}

/**
 * Represents an IDL principal reference
 */
export class PrincipalClass extends PrimitiveType<PrincipalId> {
  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitPrincipal(this, d);
  }

  public covariant(x: any): x is PrincipalId {
    return x && x._isPrincipal;
  }

  public encodeValue(x: PrincipalId): Buffer {
    const hex = x.toHex();
    const buf = Buffer.from(hex, 'hex');
    const len = lebEncode(buf.length);
    return Buffer.concat([Buffer.from([1]), len, buf]);
  }

  public encodeType() {
    return slebEncode(IDLTypeIds.Principal);
  }

  public decodeValue(b: Pipe, t: Type): PrincipalId {
    this.checkType(t);
    return decodePrincipalId(b);
  }

  get name() {
    return 'principal';
  }
  public valueToString(x: PrincipalId) {
    return `${this.name} "${x.toText()}"`;
  }
}

/**
 * Represents an IDL function reference.
 * @param argTypes Argument types.
 * @param retTypes Return types.
 * @param annotations Function annotations.
 */
export class FuncClass extends ConstructType<[PrincipalId, string]> {
  public static argsToString(types: Type[], v: any[]) {
    if (types.length !== v.length) {
      throw new Error('arity mismatch');
    }
    return '(' + types.map((t, i) => t.valueToString(v[i])).join(', ') + ')';
  }

  constructor(public argTypes: Type[], public retTypes: Type[], public annotations: string[] = []) {
    super();
  }

  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitFunc(this, d);
  }
  public covariant(x: any): x is [PrincipalId, string] {
    return (
      Array.isArray(x) && x.length === 2 && x[0] && x[0]._isPrincipal && typeof x[1] === 'string'
    );
  }

  public encodeValue(x: [PrincipalId, string]): Buffer {
    const hex = x[0].toHex();
    const buf = Buffer.from(hex, 'hex');
    const len = lebEncode(buf.length);
    const canister = Buffer.concat([Buffer.from([1]), len, buf]);

    const method = Buffer.from(x[1], 'utf8');
    const methodLen = lebEncode(method.length);
    return Buffer.concat([Buffer.from([1]), canister, methodLen, method]);
  }

  public _buildTypeTableImpl(T: TypeTable) {
    this.argTypes.forEach(arg => arg.buildTypeTable(T));
    this.retTypes.forEach(arg => arg.buildTypeTable(T));

    const opCode = slebEncode(IDLTypeIds.Func);
    const argLen = lebEncode(this.argTypes.length);
    const args = Buffer.concat(this.argTypes.map(arg => arg.encodeType(T)));
    const retLen = lebEncode(this.retTypes.length);
    const rets = Buffer.concat(this.retTypes.map(arg => arg.encodeType(T)));
    const annLen = lebEncode(this.annotations.length);
    const anns = Buffer.concat(this.annotations.map(a => this.encodeAnnotation(a)));

    T.add(this, Buffer.concat([opCode, argLen, args, retLen, rets, annLen, anns]));
  }

  public decodeValue(b: Pipe): [PrincipalId, string] {
    const x = safeRead(b, 1).toString('hex');
    if (x !== '01') {
      throw new Error('Cannot decode function reference');
    }
    const canister = decodePrincipalId(b);

    const mLen = lebDecode(b).toNumber();
    const buf = safeRead(b, mLen);
    if (!isValidUTF8(buf)) {
      throw new Error('Not valid UTF8 method name');
    }
    const method = buf.toString('utf8');
    return [canister, method];
  }

  get name() {
    const args = this.argTypes.map(arg => arg.name).join(', ');
    const rets = this.retTypes.map(arg => arg.name).join(', ');
    const annon = ' ' + this.annotations.join(' ');
    return `(${args}) -> (${rets})${annon}`;
  }

  public valueToString([principal, str]: [PrincipalId, string]) {
    return `func "${principal.toText()}".${str}`;
  }

  public display(): string {
    const args = this.argTypes.map(arg => arg.display()).join(', ');
    const rets = this.retTypes.map(arg => arg.display()).join(', ');
    const annon = ' ' + this.annotations.join(' ');
    return `(${args}) → (${rets})${annon}`;
  }

  private encodeAnnotation(ann: string): Buffer {
    if (ann === 'query') {
      return Buffer.from([1]);
    } else if (ann === 'oneway') {
      return Buffer.from([2]);
    } else {
      throw new Error('Illeagal function annotation');
    }
  }
}

export class ServiceClass extends ConstructType<PrincipalId> {
  public readonly _fields: Array<[string, FuncClass]>;
  constructor(fields: Record<string, FuncClass>) {
    super();
    this._fields = Object.entries(fields).sort((a, b) => idlLabelToId(a[0]) - idlLabelToId(b[0]));
  }
  public accept<D, R>(v: Visitor<D, R>, d: D): R {
    return v.visitService(this, d);
  }
  public covariant(x: any): x is PrincipalId {
    return x && x._isPrincipal;
  }

  public encodeValue(x: PrincipalId): Buffer {
    const hex = x.toHex();
    const buf = Buffer.from(hex, 'hex');
    const len = lebEncode(buf.length);
    return Buffer.concat([Buffer.from([1]), len, buf]);
  }

  public _buildTypeTableImpl(T: TypeTable) {
    this._fields.forEach(([_, func]) => func.buildTypeTable(T));
    const opCode = slebEncode(IDLTypeIds.Service);
    const len = lebEncode(this._fields.length);
    const meths = this._fields.map(([label, func]) => {
      const labelBuf = Buffer.from(label, 'utf8');
      const labelLen = lebEncode(labelBuf.length);
      return Buffer.concat([labelLen, labelBuf, func.encodeType(T)]);
    });

    T.add(this, Buffer.concat([opCode, len, Buffer.concat(meths)]));
  }

  public decodeValue(b: Pipe): PrincipalId {
    return decodePrincipalId(b);
  }
  get name() {
    const fields = this._fields.map(([key, value]) => key + ':' + value.name);
    return `service {${fields.join('; ')}}`;
  }

  public valueToString(x: PrincipalId) {
    return `service "${x.toText()}"`;
  }
}

/**
 * Encode a array of values
 * @returns {Buffer} serialised value
 */
export function encode(argTypes: Array<Type<any>>, args: any[]) {
  if (args.length < argTypes.length) {
    throw Error('Wrong number of message arguments');
  }

  const typeTable = new TypeTable();
  argTypes.forEach(t => t.buildTypeTable(typeTable));

  const magic = Buffer.from(magicNumber, 'utf8');
  const table = typeTable.encode();
  const len = lebEncode(args.length);
  const typs = Buffer.concat(argTypes.map(t => t.encodeType(typeTable)));
  const vals = Buffer.concat(
    zipWith(argTypes, args, (t, x) => {
      if (!t.covariant(x)) {
        throw new Error(`Invalid ${t.display()} argument: "${JSON.stringify(x)}"`);
      }

      return t.encodeValue(x);
    }),
  );

  return Buffer.concat([magic, table, len, typs, vals]);
}

/**
 * Decode a binary value
 * @param retTypes - Types expected in the buffer.
 * @param bytes - hex-encoded string, or buffer.
 * @returns Value deserialised to JS type
 */
export function decode(retTypes: Type[], bytes: Buffer): JsonValue[] {
  const b = new Pipe(bytes);

  if (bytes.byteLength < magicNumber.length) {
    throw new Error('Message length smaller than magic number');
  }
  const magic = safeRead(b, magicNumber.length).toString();
  if (magic !== magicNumber) {
    throw new Error('Wrong magic number: ' + magic);
  }

  function readTypeTable(pipe: Pipe): [Array<[IDLTypeIds, any]>, number[]] {
    const typeTable: Array<[IDLTypeIds, any]> = [];
    const len = lebDecode(pipe).toNumber();

    for (let i = 0; i < len; i++) {
      const ty = slebDecode(pipe).toNumber();
      switch (ty) {
        case IDLTypeIds.Opt:
        case IDLTypeIds.Vector: {
          const t = slebDecode(pipe).toNumber();
          typeTable.push([ty, t]);
          break;
        }
        case IDLTypeIds.Record:
        case IDLTypeIds.Variant: {
          const fields = [];
          let objectLength = lebDecode(pipe).toNumber();
          let prevHash;
          while (objectLength--) {
            const hash = lebDecode(pipe).toNumber();
            if (hash >= Math.pow(2, 32)) {
              throw new Error('field id out of 32-bit range');
            }
            if (typeof prevHash === 'number' && prevHash >= hash) {
              throw new Error('field id collision or not sorted');
            }
            prevHash = hash;
            const t = slebDecode(pipe).toNumber();
            fields.push([hash, t]);
          }
          typeTable.push([ty, fields]);
          break;
        }
        case IDLTypeIds.Func: {
          for (let k = 0; k < 2; k++) {
            let funcLength = lebDecode(pipe).toNumber();
            while (funcLength--) {
              slebDecode(pipe);
            }
          }
          const annLen = lebDecode(pipe).toNumber();
          safeRead(pipe, annLen);
          typeTable.push([ty, undefined]);
          break;
        }
        case IDLTypeIds.Service: {
          let servLength = lebDecode(pipe).toNumber();
          while (servLength--) {
            const l = lebDecode(pipe).toNumber();
            safeRead(pipe, l);
            slebDecode(pipe);
          }
          typeTable.push([ty, undefined]);
          break;
        }
        default:
          throw new Error('Illegal op_code: ' + ty);
      }
    }

    const rawList: number[] = [];
    const length = lebDecode(pipe).toNumber();
    for (let i = 0; i < length; i++) {
      rawList.push(slebDecode(pipe).toNumber());
    }
    return [typeTable, rawList];
  }
  const [rawTable, rawTypes] = readTypeTable(b);
  if (rawTypes.length < retTypes.length) {
    throw new Error('Wrong number of return values');
  }

  const table: RecClass[] = rawTable.map(_ => Rec());
  function getType(t: number): Type {
    if (t < -24) {
      throw new Error('future value not supported');
    }
    if (t < 0) {
      switch (t) {
        case -1:
          return Null;
        case -2:
          return Bool;
        case -3:
          return Nat;
        case -4:
          return Int;
        case -5:
          return Nat8;
        case -6:
          return Nat16;
        case -7:
          return Nat32;
        case -8:
          return Nat64;
        case -9:
          return Int8;
        case -10:
          return Int16;
        case -11:
          return Int32;
        case -12:
          return Int64;
        case -13:
          return Float32;
        case -14:
          return Float64;
        case -15:
          return Text;
        case -16:
          return Reserved;
        case -17:
          return Empty;
        case -24:
          return Principal;
        default:
          throw new Error('Illegal op_code: ' + t);
      }
    }
    if (t >= rawTable.length) {
      throw new Error('type index out of range');
    }
    return table[t];
  }
  function buildType(entry: [IDLTypeIds, any]): Type {
    switch (entry[0]) {
      case IDLTypeIds.Vector: {
        const ty = getType(entry[1]);
        return Vec(ty);
      }
      case IDLTypeIds.Opt: {
        const ty = getType(entry[1]);
        return Opt(ty);
      }
      case IDLTypeIds.Record: {
        const fields: Record<string, Type> = {};
        for (const [hash, ty] of entry[1]) {
          const name = `_${hash}_`;
          fields[name] = getType(ty);
        }
        const record = Record(fields);
        const tuple = record.tryAsTuple();
        if (Array.isArray(tuple)) {
          return Tuple(...tuple);
        } else {
          return record;
        }
      }
      case IDLTypeIds.Variant: {
        const fields: Record<string, Type> = {};
        for (const [hash, ty] of entry[1]) {
          const name = `_${hash}_`;
          fields[name] = getType(ty);
        }
        return Variant(fields);
      }
      case IDLTypeIds.Func: {
        return Func([], [], []);
      }
      case IDLTypeIds.Service: {
        return Service({});
      }
      default:
        throw new Error('Illegal op_code: ' + entry[0]);
    }
  }
  rawTable.forEach((entry, i) => {
    const t = buildType(entry);
    table[i].fill(t);
  });

  const types = rawTypes.map(t => getType(t));
  const output = retTypes.map((t, i) => {
    return t.decodeValue(b, types[i]);
  });

  // skip unused values
  for (let ind = retTypes.length; ind < types.length; ind++) {
    types[ind].decodeValue(b, types[ind]);
  }

  if (b.buffer.length > 0) {
    throw new Error('decode: Left-over bytes');
  }

  return output;
}

/**
 * An Interface Factory, normally provided by a Candid code generation.
 */
export type InterfaceFactory = (idl: {
  IDL: {
    Empty: EmptyClass;
    Reserved: ReservedClass;
    Bool: BoolClass;
    Null: NullClass;
    Text: TextClass;
    Int: IntClass;
    Nat: NatClass;

    Float32: FloatClass;
    Float64: FloatClass;

    Int8: FixedIntClass;
    Int16: FixedIntClass;
    Int32: FixedIntClass;
    Int64: FixedIntClass;

    Nat8: FixedNatClass;
    Nat16: FixedNatClass;
    Nat32: FixedNatClass;
    Nat64: FixedNatClass;

    Principal: PrincipalClass;

    Tuple: typeof Tuple;
    Vec: typeof Vec;
    Opt: typeof Opt;
    Record: typeof Record;
    Variant: typeof Variant;
    Rec: typeof Rec;
    Func: typeof Func;

    Service(t: Record<string, FuncClass>): ServiceClass;
  };
}) => ServiceClass;

// Export Types instances.
export const Empty = new EmptyClass();
export const Reserved = new ReservedClass();
export const Bool = new BoolClass();
export const Null = new NullClass();
export const Text = new TextClass();
export const Int = new IntClass();
export const Nat = new NatClass();

export const Float32 = new FloatClass(32);
export const Float64 = new FloatClass(64);

export const Int8 = new FixedIntClass(8);
export const Int16 = new FixedIntClass(16);
export const Int32 = new FixedIntClass(32);
export const Int64 = new FixedIntClass(64);

export const Nat8 = new FixedNatClass(8);
export const Nat16 = new FixedNatClass(16);
export const Nat32 = new FixedNatClass(32);
export const Nat64 = new FixedNatClass(64);

export const Principal = new PrincipalClass();

export function Tuple<T extends any[]>(...types: T): TupleClass<T> {
  return new TupleClass(types);
}
export function Vec<T>(t: Type<T>): VecClass<T> {
  return new VecClass(t);
}
export function Opt<T>(t: Type<T>): OptClass<T> {
  return new OptClass(t);
}

export function Record(t: Record<string, Type>): RecordClass {
  return new RecordClass(t);
}
export function Variant(fields: Record<string, Type>) {
  return new VariantClass(fields);
}
export function Rec() {
  return new RecClass();
}

export function Func(args: Type[], ret: Type[], annotations: string[] = []) {
  return new FuncClass(args, ret, annotations);
}

export function Service(t: Record<string, FuncClass>): ServiceClass {
  return new ServiceClass(t);
}
