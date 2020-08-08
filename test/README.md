Candid test data
================

This directory contains Candid test data, to be used to check Candid
implementations for compliance.

This test suite covers

 * parsing Candid service descriptions
 * given a Candid type, decoding binary Candid data, asserting success or failure
 * given a Candid type, decoding textual Candid data, asserting success or failure

Because this test data necessarily has to be host-language agnostic, it is not
possible to

 * assert the decoded value, as it would be host-language specific
 * cover encoding, as it would require specifying a host-language value,
   and also because Candid encoding is not canonical

Implementers are advised to extend this test suite with randomzied
round-tripping tests (host value → candid → host value).

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
   <test> = <argseq> <input> <outcome> <desc>
   <argseq>  ::= ( <argtype>,* )
   <input> =  <text> | blob <text>
   <outcome> = true | false
   <desc> = <text>?
   ```
   where
     * `<argseq>` describes the type to decode the value at
     * `<input>` describes input in textual notation (`<text>`) or binary
       format (`blob <text>)`
     * `<outcome>` describes the expected outcome of decoding the input:
       decoding should either succeed (`true`) or fail (`false`)
     * `<desc>` is an optional description of the test, potentially useful in
       error messages

A Candid implementation conforms to this test suite if

 * its service parser (if present) accepts all `*.good.did` files and rejects
   all `*.bad.did` files in this directory.
 * it can parse all binary input from all `*.test.did` files at the given types
 * it can parse all test input from all `*.test.did` files at the given types
   (if it supports parsing the textual representation).
 
