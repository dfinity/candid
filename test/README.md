Candid test data
================

This directory contains Candid test data, to be used to check Candid
implementations for compliance.

This test suite covers

 * parsing Candid service descriptions
 * given a Candid type, decoding binary Candid data, asserting success or failure
 * given a Candid type, parsing textual Candid data, asserting success or failure
 * comparing such decoded/parsed values, using the Host language’s notion of equality.

The test suite currently does not cover _encoding_, because the Candid binary
format is not canonical.  Implementers are advised to extend this test suite
with randomzied round-tripping tests (host value → candid → host value) to
cover encoding as well.

Format
======

The test suite contains these kind of files:

 * `<name>.good.did`:
   A Candid service description, with valid candid syntax.
   Implementations should be able to parse them.

 * `<name>.bad.did`:
   A Candid service description, with invalid candid syntax.
   Implementations should reject parsing them.

 * `<name>.test.did`:
   A set of Candid tests, written in a grammar that extends the Candid type and value grammar:

   The root production is
   ```
   <enctest>  ::= <def>;* <test>;*
   ```
   to allow any number of type definitions followed by encoding tests with grammar
   ```
   <test> ::=
      | assert <input> : <tuptype> <desc>
      | assert <input> !: <tuptype> <desc>
      | assert <input> == <input> : <tuptype> <desc>
      | assert <input> != <input> : <tuptype> <desc>
   <input> ::= <text> | blob <text>
   <desc> ::=  <text>?
   ```
   where the four forms assert
    * that the input can be decoded/parsed at that type
    * that the input cannot be decoded/parsed at that type
    * that the two inputs values decode/parse successfully,
      and the results are equal.
    * that the two inputs values decode/parse successfully,
      and the results are not equal.

   The last two forms refer to the host language's equality, and are useful to
   assert that due to subtyping, certain information is ignored.

   The `<input>` describes input in textual notation (`<text>`) or binary
   format (`blob <text>`).

   A `<desc>` is an optional description of the test, potentially useful in
   the test suite output.

A Candid implementation conforms to this test suite if

 * its service parser (if present) accepts all `*.good.did` files and rejects
   all `*.bad.did` files in this directory.
 * all tests from all `*.test.did` files succeed.

Candid implementations that do not support parsing service files can ignore the
`*.good.did` and `*.bad.did` files.

Candid implementations that do not support parsing the textual prepresentation
can ignore those tests where all inputs are textual. They should treat a test
that compares textual and binary values as plain decoding assertions on the
binary value.

For example, `assert blob "DIDL\00\01\7e\00" == (true) : (bool)` should be
treated as `assert blob "DIDL\00\01\7e\00" : (bool)` by such an implementation.
