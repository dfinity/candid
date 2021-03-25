import { idlLabelToId } from './hash';

test('IDL label', () => {
  function testLabel(str: string, expected: number) {
    expect(idlLabelToId(str)).toBe(expected);
  }

  testLabel('', 0);
  testLabel('id', 23515);
  testLabel('description', 1595738364);
  testLabel('short_name', 3261810734);
  testLabel('Hi ☃', 1419229646);
  testLabel('_0_', 0);
  testLabel('_1_', 1);
  testLabel('_+1_', 1055658234);
  testLabel('_-1_', 1055757692);
  testLabel('_123_', 123);
  testLabel('_4294967295_', 4294967295);
  testLabel('_4294967296_', 1569808370);
  testLabel('_0xa_', 10);
  testLabel('_0d_', 1055918252);
  testLabel('_1.23_', 1360503298);
  testLabel('_1e2_', 3552665568);
  testLabel('_', 95);
  testLabel('__', 21280);
  testLabel('___', 4745535);
});
