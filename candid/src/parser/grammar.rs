// auto-generated: "lalrpop 0.19.0"
// sha256: 5153bd68bb2b569d95e8116f8b8e7dd38947bf96546faef2429624e57e82da3
use super::value::{IDLField, IDLValue, IDLArgs};
use super::types::{IDLType, PrimType, Label, TypeField, FuncType, FuncMode, Binding, Dec, IDLProg};
use super::lexer::{Token, LexicalError, TmpIDLField};
use crate::idl_hash;
#[allow(unused_extern_crates)]
extern crate lalrpop_util as __lalrpop_util;
#[allow(unused_imports)]
use self::__lalrpop_util::state_machine as __state_machine;

#[cfg_attr(rustfmt, rustfmt_skip)]
mod __parse__Args {
    #![allow(non_snake_case, non_camel_case_types, unused_mut, unused_variables, unused_imports, unused_parens)]

    use super::super::value::{IDLField, IDLValue, IDLArgs};
    use super::super::types::{IDLType, PrimType, Label, TypeField, FuncType, FuncMode, Binding, Dec, IDLProg};
    use super::super::lexer::{Token, LexicalError, TmpIDLField};
    use crate::idl_hash;
    #[allow(unused_extern_crates)]
    extern crate lalrpop_util as __lalrpop_util;
    #[allow(unused_imports)]
    use self::__lalrpop_util::state_machine as __state_machine;
    use super::__ToTriple;
    #[allow(dead_code)]
    pub enum __Symbol<>
     {
        Variant0(Token),
        Variant1(bool),
        Variant2(String),
        Variant3(::std::option::Option<String>),
        Variant4(IDLValue),
        Variant5(::std::vec::Vec<IDLValue>),
        Variant6(IDLType),
        Variant7(::std::vec::Vec<IDLType>),
        Variant8(Dec),
        Variant9(::std::vec::Vec<Dec>),
        Variant10(Binding),
        Variant11(::std::vec::Vec<Binding>),
        Variant12(TmpIDLField),
        Variant13(::std::vec::Vec<TmpIDLField>),
        Variant14(TypeField),
        Variant15(::std::vec::Vec<TypeField>),
        Variant16(::std::option::Option<IDLType>),
        Variant17(Vec<Binding>),
        Variant18(::std::option::Option<IDLValue>),
        Variant19(IDLArgs),
        Variant20(::std::option::Option<Dec>),
        Variant21(IDLField),
        Variant22(FuncMode),
        Variant23(::std::vec::Vec<FuncMode>),
        Variant24(FuncType),
        Variant25(IDLProg),
        Variant26(::std::option::Option<Binding>),
        Variant27(::std::option::Option<TmpIDLField>),
        Variant28(::std::option::Option<TypeField>),
        Variant29(Vec<IDLValue>),
        Variant30(Vec<IDLType>),
        Variant31(Vec<Dec>),
        Variant32(Vec<TmpIDLField>),
        Variant33(Vec<TypeField>),
    }
    const __ACTION: &[i16] = &[
        // State 0
        2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 1
        0, -103, 15, 0, 16, 0, 0, 0, 0, 0, 17, 0, 0, 0, 18, 19, 20, 0, 4, 0, 21, 0, 22, 0, 23, 24, 0, 0,
        // State 2
        0, -105, 15, 0, 16, 0, 0, 0, 0, 0, 17, 0, 0, 0, 18, 19, 20, 0, 4, 0, 21, 0, 22, 0, 23, 24, 0, 0,
        // State 3
        0, 0, 15, 0, 16, 0, 0, 0, 0, 0, 17, 0, 0, 0, 18, 19, 20, 0, 4, 0, 21, 0, 22, 0, 23, 24, 0, 0,
        // State 4
        0, 0, 15, 0, 16, 0, 0, 0, 0, 0, 17, 0, 37, 0, 18, 19, 38, 0, 4, 0, 21, 0, 39, 0, 23, 24, 0, -123,
        // State 5
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 43, 0, 0, 0, 0, 0, 44, 0, 0, 0, 0, 0,
        // State 6
        0, 0, 15, 0, 16, 0, 0, 0, 0, 0, 17, 0, 0, 0, 18, 19, 20, 0, 4, 0, 21, 0, 22, 0, 23, 24, 0, -107,
        // State 7
        0, 0, 15, 0, 16, 0, 0, 0, 0, 0, 17, 0, 37, 0, 18, 19, 38, 0, 4, 0, 21, 0, 39, 0, 23, 24, 0, -125,
        // State 8
        0, 0, 15, 0, 16, 0, 0, 0, 0, 0, 17, 0, 0, 0, 18, 19, 20, 0, 4, 0, 21, 0, 22, 0, 23, 24, 0, -109,
        // State 9
        0, 0, 15, 0, 16, 0, 0, 0, 0, 0, 17, 0, 0, 0, 18, 19, 20, 0, 4, 0, 21, 0, 22, 0, 23, 24, 0, 0,
        // State 10
        0, 0, 15, 0, 16, 0, 0, 0, 0, 0, 17, 0, 0, 0, 18, 19, 20, 0, 4, 0, 21, 0, 22, 0, 23, 24, 0, 0,
        // State 11
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 12
        0, -102, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 13
        0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 14
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 15
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 16
        0, -50, 0, -50, 0, 0, 0, -50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -50,
        // State 17
        0, -56, 0, -56, 0, 0, 0, -56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -56,
        // State 18
        0, -55, 0, -55, 0, 0, 0, -55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -55,
        // State 19
        0, -53, 0, -53, 0, 0, 0, -53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -53,
        // State 20
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0,
        // State 21
        0, -54, 0, -54, 0, 0, 0, -54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -54,
        // State 22
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0,
        // State 23
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0,
        // State 24
        0, -104, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 25
        0, -6, -6, 0, -6, 0, 0, 0, 0, 0, -6, 0, 0, 0, -6, -6, -6, 0, -6, 0, -6, 0, -6, 0, -6, -6, 0, 0,
        // State 26
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 27
        0, -51, 0, -51, 0, 0, 0, -51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -51,
        // State 28
        0, -52, 0, -52, 0, 0, 0, -52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -52,
        // State 29
        0, -57, 0, -57, 0, 0, 0, -57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -57,
        // State 30
        0, -7, -7, 0, -7, 0, 0, 0, 0, 0, -7, 0, 0, 0, -7, -7, -7, 0, -7, 0, -7, 0, -7, 0, -7, -7, 0, 0,
        // State 31
        0, 0, 0, 0, 0, 0, 0, -95, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -95,
        // State 32
        0, 0, 0, 0, 0, 0, 0, -94, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -94,
        // State 33
        0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 34
        0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -122,
        // State 35
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49,
        // State 36
        0, 0, 0, 0, 0, 0, 0, 0, -90, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -90,
        // State 37
        0, 0, 0, 0, 0, 0, 0, -53, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -53,
        // State 38
        0, 0, 0, 0, 0, 0, 0, -54, -91, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -54,
        // State 39
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -142,
        // State 40
        0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -143,
        // State 41
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50,
        // State 42
        0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -144,
        // State 43
        0, 0, 0, 0, 0, 0, 0, 0, -91, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -91,
        // State 44
        0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -106,
        // State 45
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53,
        // State 46
        0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -124,
        // State 47
        0, 0, -31, 0, -31, 0, 0, 0, 0, 0, -31, 0, -31, 0, -31, -31, -31, 0, -31, 0, -31, 0, -31, 0, -31, -31, 0, -31,
        // State 48
        0, -59, 0, -59, 0, 0, 0, -59, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -59,
        // State 49
        0, -60, 0, -60, 0, 0, 0, -60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -60,
        // State 50
        0, 0, 0, 0, 0, 0, 0, 57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -108,
        // State 51
        0, 0, -11, 0, -11, 0, 0, 0, 0, 0, -11, 0, 0, 0, -11, -11, -11, 0, -11, 0, -11, 0, -11, 0, -11, -11, 0, -11,
        // State 52
        0, -58, 0, -58, 0, 0, 0, -58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -58,
        // State 53
        0, 0, -32, 0, -32, 0, 0, 0, 0, 0, -32, 0, -32, 0, -32, -32, -32, 0, -32, 0, -32, 0, -32, 0, -32, -32, 0, -32,
        // State 54
        0, 0, 0, 0, 0, 0, 0, -73, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -73,
        // State 55
        0, 0, 0, 0, 0, 0, 0, -72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -72,
        // State 56
        0, 0, -12, 0, -12, 0, 0, 0, 0, 0, -12, 0, 0, 0, -12, -12, -12, 0, -12, 0, -12, 0, -12, 0, -12, -12, 0, -12,
    ];
    fn __action(state: i16, integer: usize) -> i16 {
        __ACTION[(state as usize) * 28 + integer]
    }
    const __EOF_ACTION: &[i16] = &[
        // State 0
        0,
        // State 1
        0,
        // State 2
        0,
        // State 3
        0,
        // State 4
        0,
        // State 5
        0,
        // State 6
        0,
        // State 7
        0,
        // State 8
        0,
        // State 9
        0,
        // State 10
        0,
        // State 11
        -150,
        // State 12
        0,
        // State 13
        0,
        // State 14
        0,
        // State 15
        0,
        // State 16
        0,
        // State 17
        0,
        // State 18
        0,
        // State 19
        0,
        // State 20
        0,
        // State 21
        0,
        // State 22
        0,
        // State 23
        0,
        // State 24
        0,
        // State 25
        0,
        // State 26
        -67,
        // State 27
        0,
        // State 28
        0,
        // State 29
        0,
        // State 30
        0,
        // State 31
        0,
        // State 32
        0,
        // State 33
        0,
        // State 34
        0,
        // State 35
        0,
        // State 36
        0,
        // State 37
        0,
        // State 38
        0,
        // State 39
        0,
        // State 40
        0,
        // State 41
        0,
        // State 42
        0,
        // State 43
        0,
        // State 44
        0,
        // State 45
        0,
        // State 46
        0,
        // State 47
        0,
        // State 48
        0,
        // State 49
        0,
        // State 50
        0,
        // State 51
        0,
        // State 52
        0,
        // State 53
        0,
        // State 54
        0,
        // State 55
        0,
        // State 56
        0,
    ];
    fn __goto(state: i16, nt: usize) -> i16 {
        match nt {
            3 => 2,
            6 => 8,
            18 => 7,
            28 => match state {
                1 => 12,
                2 => 24,
                3 => 29,
                6 => 44,
                8 => 50,
                9 => 54,
                10 => 55,
                _ => 31,
            },
            32 => 11,
            35 => match state {
                5 => 39,
                _ => 32,
            },
            44 => match state {
                5 => 40,
                _ => 33,
            },
            46 => match state {
                7 => 46,
                _ => 34,
            },
            50 => 13,
            51 => 45,
            55 => 35,
            59 => 41,
            _ => 0,
        }
    }
    fn __expected_tokens(__state: i16) -> Vec<::std::string::String> {
        const __TERMINAL: &[&str] = &[
            r###""(""###,
            r###"")""###,
            r###""+""###,
            r###"",""###,
            r###""-""###,
            r###""->""###,
            r###"":""###,
            r###"";""###,
            r###""=""###,
            r###""blob""###,
            r###""bool""###,
            r###""func""###,
            r###""id""###,
            r###""import""###,
            r###""none""###,
            r###""null""###,
            r###""number""###,
            r###""oneway""###,
            r###""opt""###,
            r###""query""###,
            r###""record""###,
            r###""service""###,
            r###""text""###,
            r###""type""###,
            r###""variant""###,
            r###""vec""###,
            r###""{""###,
            r###""}""###,
        ];
        __TERMINAL.iter().enumerate().filter_map(|(index, terminal)| {
            let next_state = __action(__state, index);
            if next_state == 0 {
                None
            } else {
                Some(terminal.to_string())
            }
        }).collect()
    }
    pub struct __StateMachine<>
    where 
    {
        __phantom: ::std::marker::PhantomData<()>,
    }
    impl<> __state_machine::ParserDefinition for __StateMachine<>
    where 
    {
        type Location = usize;
        type Error = LexicalError;
        type Token = Token;
        type TokenIndex = usize;
        type Symbol = __Symbol<>;
        type Success = IDLArgs;
        type StateIndex = i16;
        type Action = i16;
        type ReduceIndex = i16;
        type NonterminalIndex = usize;

        #[inline]
        fn start_location(&self) -> Self::Location {
              Default::default()
        }

        #[inline]
        fn start_state(&self) -> Self::StateIndex {
              0
        }

        #[inline]
        fn token_to_index(&self, token: &Self::Token) -> Option<usize> {
            __token_to_integer(token, ::std::marker::PhantomData::<()>)
        }

        #[inline]
        fn action(&self, state: i16, integer: usize) -> i16 {
            __action(state, integer)
        }

        #[inline]
        fn error_action(&self, state: i16) -> i16 {
            __action(state, 28 - 1)
        }

        #[inline]
        fn eof_action(&self, state: i16) -> i16 {
            __EOF_ACTION[state as usize]
        }

        #[inline]
        fn goto(&self, state: i16, nt: usize) -> i16 {
            __goto(state, nt)
        }

        fn token_to_symbol(&self, token_index: usize, token: Self::Token) -> Self::Symbol {
            __token_to_symbol(token_index, token, ::std::marker::PhantomData::<()>)
        }

        fn expected_tokens(&self, state: i16) -> Vec<String> {
            __expected_tokens(state)
        }

        #[inline]
        fn uses_error_recovery(&self) -> bool {
            false
        }

        #[inline]
        fn error_recovery_symbol(
            &self,
            recovery: __state_machine::ErrorRecovery<Self>,
        ) -> Self::Symbol {
            panic!("error recovery not enabled for this grammar")
        }

        fn reduce(
            &mut self,
            action: i16,
            start_location: Option<&Self::Location>,
            states: &mut Vec<i16>,
            symbols: &mut Vec<__state_machine::SymbolTriple<Self>>,
        ) -> Option<__state_machine::ParseResult<Self>> {
            __reduce(
                action,
                start_location,
                states,
                symbols,
                ::std::marker::PhantomData::<()>,
            )
        }

        fn simulate_reduce(&self, action: i16) -> __state_machine::SimulatedReduce<Self> {
            panic!("error recovery not enabled for this grammar")
        }
    }
    fn __token_to_integer<
    >(
        __token: &Token,
        _: ::std::marker::PhantomData<()>,
    ) -> Option<usize>
    {
        match *__token {
            Token::LParen if true => Some(0),
            Token::RParen if true => Some(1),
            Token::Plus if true => Some(2),
            Token::Comma if true => Some(3),
            Token::Minus if true => Some(4),
            Token::Arrow if true => Some(5),
            Token::Colon if true => Some(6),
            Token::Semi if true => Some(7),
            Token::Equals if true => Some(8),
            Token::Blob if true => Some(9),
            Token::Boolean(_) if true => Some(10),
            Token::Func if true => Some(11),
            Token::Id(_) if true => Some(12),
            Token::Import if true => Some(13),
            Token::None if true => Some(14),
            Token::Null if true => Some(15),
            Token::Number(_) if true => Some(16),
            Token::Oneway if true => Some(17),
            Token::Opt if true => Some(18),
            Token::Query if true => Some(19),
            Token::Record if true => Some(20),
            Token::Service if true => Some(21),
            Token::Text(_) if true => Some(22),
            Token::Type if true => Some(23),
            Token::Variant if true => Some(24),
            Token::Vec if true => Some(25),
            Token::LBrace if true => Some(26),
            Token::RBrace if true => Some(27),
            _ => None,
        }
    }
    fn __token_to_symbol<
    >(
        __token_index: usize,
        __token: Token,
        _: ::std::marker::PhantomData<()>,
    ) -> __Symbol<>
    {
        match __token_index {
            0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 11 | 13 | 14 | 15 | 17 | 18 | 19 | 20 | 21 | 23 | 24 | 25 | 26 | 27 => __Symbol::Variant0(__token),
            10 => match __token {
                Token::Boolean(__tok0) if true => __Symbol::Variant1(__tok0),
                _ => unreachable!(),
            },
            12 | 16 | 22 => match __token {
                Token::Id(__tok0) | Token::Number(__tok0) | Token::Text(__tok0) if true => __Symbol::Variant2(__tok0),
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }
    pub struct ArgsParser {
        _priv: (),
    }

    impl ArgsParser {
        pub fn new() -> ArgsParser {
            ArgsParser {
                _priv: (),
            }
        }

        #[allow(dead_code)]
        pub fn parse<
            __TOKEN: __ToTriple<>,
            __TOKENS: IntoIterator<Item=__TOKEN>,
        >(
            &self,
            __tokens0: __TOKENS,
        ) -> Result<IDLArgs, __lalrpop_util::ParseError<usize, Token, LexicalError>>
        {
            let __tokens = __tokens0.into_iter();
            let mut __tokens = __tokens.map(|t| __ToTriple::to_triple(t));
            __state_machine::Parser::drive(
                __StateMachine {
                    __phantom: ::std::marker::PhantomData::<()>,
                },
                __tokens,
            )
        }
    }
    pub(crate) fn __reduce<
    >(
        __action: i16,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i16>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> Option<Result<IDLArgs,__lalrpop_util::ParseError<usize, Token, LexicalError>>>
    {
        let (__pop_states, __nonterminal) = match __action {
            0 => {
                __reduce0(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            1 => {
                __reduce1(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            2 => {
                __reduce2(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            3 => {
                __reduce3(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            4 => {
                __reduce4(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            5 => {
                __reduce5(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            6 => {
                __reduce6(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            7 => {
                __reduce7(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            8 => {
                __reduce8(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            9 => {
                __reduce9(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            10 => {
                __reduce10(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            11 => {
                __reduce11(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            12 => {
                __reduce12(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            13 => {
                __reduce13(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            14 => {
                __reduce14(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            15 => {
                __reduce15(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            16 => {
                __reduce16(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            17 => {
                __reduce17(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            18 => {
                __reduce18(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            19 => {
                __reduce19(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            20 => {
                __reduce20(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            21 => {
                __reduce21(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            22 => {
                __reduce22(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            23 => {
                __reduce23(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            24 => {
                __reduce24(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            25 => {
                __reduce25(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            26 => {
                __reduce26(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            27 => {
                __reduce27(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            28 => {
                __reduce28(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            29 => {
                __reduce29(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            30 => {
                __reduce30(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            31 => {
                __reduce31(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            32 => {
                __reduce32(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            33 => {
                __reduce33(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            34 => {
                __reduce34(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            35 => {
                __reduce35(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            36 => {
                __reduce36(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            37 => {
                __reduce37(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            38 => {
                __reduce38(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            39 => {
                __reduce39(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            40 => {
                __reduce40(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            41 => {
                __reduce41(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            42 => {
                __reduce42(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            43 => {
                __reduce43(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            44 => {
                __reduce44(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            45 => {
                __reduce45(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            46 => {
                __reduce46(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            47 => {
                __reduce47(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            48 => {
                __reduce48(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            49 => {
                __reduce49(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            50 => {
                __reduce50(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            51 => {
                __reduce51(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            52 => {
                __reduce52(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            53 => {
                __reduce53(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            54 => {
                __reduce54(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            55 => {
                __reduce55(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            56 => {
                __reduce56(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            57 => {
                __reduce57(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            58 => {
                __reduce58(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            59 => {
                __reduce59(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            60 => {
                __reduce60(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            61 => {
                __reduce61(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            62 => {
                __reduce62(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            63 => {
                __reduce63(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            64 => {
                __reduce64(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            65 => {
                __reduce65(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            66 => {
                __reduce66(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            67 => {
                __reduce67(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            68 => {
                __reduce68(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            69 => {
                __reduce69(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            70 => {
                __reduce70(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            71 => {
                __reduce71(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            72 => {
                __reduce72(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            73 => {
                __reduce73(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            74 => {
                __reduce74(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            75 => {
                __reduce75(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            76 => {
                __reduce76(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            77 => {
                __reduce77(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            78 => {
                __reduce78(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            79 => {
                __reduce79(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            80 => {
                __reduce80(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            81 => {
                __reduce81(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            82 => {
                __reduce82(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            83 => {
                __reduce83(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            84 => {
                __reduce84(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            85 => {
                __reduce85(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            86 => {
                __reduce86(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            87 => {
                __reduce87(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            88 => {
                __reduce88(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            89 => {
                __reduce89(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            90 => {
                __reduce90(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            91 => {
                __reduce91(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            92 => {
                __reduce92(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            93 => {
                __reduce93(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            94 => {
                __reduce94(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            95 => {
                __reduce95(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            96 => {
                __reduce96(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            97 => {
                __reduce97(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            98 => {
                __reduce98(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            99 => {
                __reduce99(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            100 => {
                __reduce100(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            101 => {
                __reduce101(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            102 => {
                __reduce102(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            103 => {
                __reduce103(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            104 => {
                __reduce104(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            105 => {
                __reduce105(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            106 => {
                __reduce106(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            107 => {
                __reduce107(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            108 => {
                __reduce108(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            109 => {
                __reduce109(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            110 => {
                __reduce110(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            111 => {
                __reduce111(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            112 => {
                __reduce112(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            113 => {
                __reduce113(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            114 => {
                __reduce114(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            115 => {
                __reduce115(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            116 => {
                __reduce116(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            117 => {
                __reduce117(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            118 => {
                __reduce118(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            119 => {
                __reduce119(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            120 => {
                __reduce120(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            121 => {
                __reduce121(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            122 => {
                __reduce122(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            123 => {
                __reduce123(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            124 => {
                __reduce124(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            125 => {
                __reduce125(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            126 => {
                __reduce126(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            127 => {
                __reduce127(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            128 => {
                __reduce128(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            129 => {
                __reduce129(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            130 => {
                __reduce130(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            131 => {
                __reduce131(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            132 => {
                __reduce132(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            133 => {
                __reduce133(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            134 => {
                __reduce134(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            135 => {
                __reduce135(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            136 => {
                __reduce136(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            137 => {
                __reduce137(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            138 => {
                __reduce138(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            139 => {
                __reduce139(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            140 => {
                __reduce140(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            141 => {
                __reduce141(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            142 => {
                __reduce142(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            143 => {
                __reduce143(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            144 => {
                __reduce144(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            145 => {
                __reduce145(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            146 => {
                __reduce146(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            147 => {
                __reduce147(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            148 => {
                __reduce148(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            149 => {
                // __Args = Args => ActionFn(0);
                let __sym0 = __pop_Variant19(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action0::<>(__sym0);
                return Some(Ok(__nt));
            }
            150 => {
                __reduce150(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            _ => panic!("invalid action code {}", __action)
        };
        let __states_len = __states.len();
        __states.truncate(__states_len - __pop_states);
        let __state = *__states.last().unwrap();
        let __next_state = __goto(__state, __nonterminal);
        __states.push(__next_state);
        None
    }
    #[inline(never)]
    fn __symbol_type_mismatch() -> ! {
        panic!("symbol type mismatch")
    }
    fn __pop_Variant10<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Binding, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant10(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant8<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Dec, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant8(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant22<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, FuncMode, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant22(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant24<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, FuncType, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant24(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant19<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, IDLArgs, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant19(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant21<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, IDLField, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant21(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant25<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, IDLProg, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant25(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant6<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, IDLType, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant6(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant4<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, IDLValue, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant4(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant2<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, String, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant2(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant12<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, TmpIDLField, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant12(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant0<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Token, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant0(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant14<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, TypeField, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant14(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant17<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Vec<Binding>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant17(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant31<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Vec<Dec>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant31(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant30<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Vec<IDLType>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant30(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant29<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Vec<IDLValue>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant29(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant32<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Vec<TmpIDLField>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant32(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant33<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Vec<TypeField>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant33(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant1<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, bool, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant1(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant26<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::option::Option<Binding>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant26(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant20<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::option::Option<Dec>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant20(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant16<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::option::Option<IDLType>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant16(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant18<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::option::Option<IDLValue>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant18(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant3<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::option::Option<String>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant3(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant27<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::option::Option<TmpIDLField>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant27(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant28<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::option::Option<TypeField>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant28(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant11<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::vec::Vec<Binding>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant11(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant9<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::vec::Vec<Dec>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant9(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant23<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::vec::Vec<FuncMode>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant23(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant7<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::vec::Vec<IDLType>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant7(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant5<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::vec::Vec<IDLValue>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant5(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant13<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::vec::Vec<TmpIDLField>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant13(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant15<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::vec::Vec<TypeField>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant15(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    pub(crate) fn __reduce0<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // "id"? = "id" => ActionFn(56);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action56::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant3(__nt), __end));
        (1, 0)
    }
    pub(crate) fn __reduce1<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // "id"? =  => ActionFn(57);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action57::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant3(__nt), __end));
        (0, 0)
    }
    pub(crate) fn __reduce2<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ",") = Arg, "," => ActionFn(69);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action69::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (2, 1)
    }
    pub(crate) fn __reduce3<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ",")* =  => ActionFn(67);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action67::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (0, 2)
    }
    pub(crate) fn __reduce4<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ",")* = (<Arg> ",")+ => ActionFn(68);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action68::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 2)
    }
    pub(crate) fn __reduce5<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ",")+ = Arg, "," => ActionFn(127);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action127::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (2, 3)
    }
    pub(crate) fn __reduce6<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ",")+ = (<Arg> ",")+, Arg, "," => ActionFn(128);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action128::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 3)
    }
    pub(crate) fn __reduce7<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ";") = Arg, ";" => ActionFn(74);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action74::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (2, 4)
    }
    pub(crate) fn __reduce8<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ";")* =  => ActionFn(72);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action72::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (0, 5)
    }
    pub(crate) fn __reduce9<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ";")* = (<Arg> ";")+ => ActionFn(73);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action73::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 5)
    }
    pub(crate) fn __reduce10<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ";")+ = Arg, ";" => ActionFn(131);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action131::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (2, 6)
    }
    pub(crate) fn __reduce11<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ";")+ = (<Arg> ";")+, Arg, ";" => ActionFn(132);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action132::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 6)
    }
    pub(crate) fn __reduce12<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<ArgTyp> ",") = ArgTyp, "," => ActionFn(94);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action94::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (2, 7)
    }
    pub(crate) fn __reduce13<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<ArgTyp> ",")* =  => ActionFn(92);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action92::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant7(__nt), __end));
        (0, 8)
    }
    pub(crate) fn __reduce14<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<ArgTyp> ",")* = (<ArgTyp> ",")+ => ActionFn(93);
        let __sym0 = __pop_Variant7(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action93::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant7(__nt), __end));
        (1, 8)
    }
    pub(crate) fn __reduce15<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<ArgTyp> ",")+ = ArgTyp, "," => ActionFn(135);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action135::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant7(__nt), __end));
        (2, 9)
    }
    pub(crate) fn __reduce16<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<ArgTyp> ",")+ = (<ArgTyp> ",")+, ArgTyp, "," => ActionFn(136);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant6(__symbols);
        let __sym0 = __pop_Variant7(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action136::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant7(__nt), __end));
        (3, 9)
    }
    pub(crate) fn __reduce17<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Def> ";") = Def, ";" => ActionFn(106);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant8(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action106::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant8(__nt), __end));
        (2, 10)
    }
    pub(crate) fn __reduce18<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Def> ";")* =  => ActionFn(104);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action104::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant9(__nt), __end));
        (0, 11)
    }
    pub(crate) fn __reduce19<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Def> ";")* = (<Def> ";")+ => ActionFn(105);
        let __sym0 = __pop_Variant9(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action105::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant9(__nt), __end));
        (1, 11)
    }
    pub(crate) fn __reduce20<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Def> ";")+ = Def, ";" => ActionFn(139);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant8(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action139::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant9(__nt), __end));
        (2, 12)
    }
    pub(crate) fn __reduce21<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Def> ";")+ = (<Def> ";")+, Def, ";" => ActionFn(140);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant8(__symbols);
        let __sym0 = __pop_Variant9(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action140::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant9(__nt), __end));
        (3, 12)
    }
    pub(crate) fn __reduce22<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<MethTyp> ";") = MethTyp, ";" => ActionFn(101);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action101::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (2, 13)
    }
    pub(crate) fn __reduce23<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<MethTyp> ";")* =  => ActionFn(99);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action99::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant11(__nt), __end));
        (0, 14)
    }
    pub(crate) fn __reduce24<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<MethTyp> ";")* = (<MethTyp> ";")+ => ActionFn(100);
        let __sym0 = __pop_Variant11(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action100::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant11(__nt), __end));
        (1, 14)
    }
    pub(crate) fn __reduce25<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<MethTyp> ";")+ = MethTyp, ";" => ActionFn(143);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action143::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant11(__nt), __end));
        (2, 15)
    }
    pub(crate) fn __reduce26<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<MethTyp> ";")+ = (<MethTyp> ";")+, MethTyp, ";" => ActionFn(144);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant10(__symbols);
        let __sym0 = __pop_Variant11(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action144::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant11(__nt), __end));
        (3, 15)
    }
    pub(crate) fn __reduce27<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordField> ";") = RecordField, ";" => ActionFn(79);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant12(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action79::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant12(__nt), __end));
        (2, 16)
    }
    pub(crate) fn __reduce28<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordField> ";")* =  => ActionFn(77);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action77::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant13(__nt), __end));
        (0, 17)
    }
    pub(crate) fn __reduce29<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordField> ";")* = (<RecordField> ";")+ => ActionFn(78);
        let __sym0 = __pop_Variant13(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action78::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant13(__nt), __end));
        (1, 17)
    }
    pub(crate) fn __reduce30<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordField> ";")+ = RecordField, ";" => ActionFn(147);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant12(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action147::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant13(__nt), __end));
        (2, 18)
    }
    pub(crate) fn __reduce31<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordField> ";")+ = (<RecordField> ";")+, RecordField, ";" => ActionFn(148);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant12(__symbols);
        let __sym0 = __pop_Variant13(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action148::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant13(__nt), __end));
        (3, 18)
    }
    pub(crate) fn __reduce32<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordFieldTyp> ";") = RecordFieldTyp, ";" => ActionFn(84);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action84::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (2, 19)
    }
    pub(crate) fn __reduce33<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordFieldTyp> ";")* =  => ActionFn(82);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action82::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (0, 20)
    }
    pub(crate) fn __reduce34<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordFieldTyp> ";")* = (<RecordFieldTyp> ";")+ => ActionFn(83);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action83::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (1, 20)
    }
    pub(crate) fn __reduce35<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordFieldTyp> ";")+ = RecordFieldTyp, ";" => ActionFn(151);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action151::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (2, 21)
    }
    pub(crate) fn __reduce36<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordFieldTyp> ";")+ = (<RecordFieldTyp> ";")+, RecordFieldTyp, ";" => ActionFn(152);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant14(__symbols);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action152::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (3, 21)
    }
    pub(crate) fn __reduce37<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<VariantFieldTyp> ";") = VariantFieldTyp, ";" => ActionFn(89);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action89::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (2, 22)
    }
    pub(crate) fn __reduce38<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<VariantFieldTyp> ";")* =  => ActionFn(87);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action87::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (0, 23)
    }
    pub(crate) fn __reduce39<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<VariantFieldTyp> ";")* = (<VariantFieldTyp> ";")+ => ActionFn(88);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action88::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (1, 23)
    }
    pub(crate) fn __reduce40<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<VariantFieldTyp> ";")+ = VariantFieldTyp, ";" => ActionFn(155);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action155::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (2, 24)
    }
    pub(crate) fn __reduce41<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<VariantFieldTyp> ";")+ = (<VariantFieldTyp> ";")+, VariantFieldTyp, ";" => ActionFn(156);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant14(__symbols);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action156::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (3, 24)
    }
    pub(crate) fn __reduce42<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Actor = "service", "id", ":", ActorTyp => ActionFn(123);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant17(__symbols);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant2(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action123::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (4, 25)
    }
    pub(crate) fn __reduce43<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Actor = "service", ":", ActorTyp => ActionFn(124);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant17(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action124::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (3, 25)
    }
    pub(crate) fn __reduce44<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Actor = "service", "id", ":", "id" => ActionFn(125);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant2(__symbols);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant2(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action125::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (4, 25)
    }
    pub(crate) fn __reduce45<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Actor = "service", ":", "id" => ActionFn(126);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant2(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action126::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (3, 25)
    }
    pub(crate) fn __reduce46<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Actor? = Actor => ActionFn(53);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action53::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant16(__nt), __end));
        (1, 26)
    }
    pub(crate) fn __reduce47<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Actor? =  => ActionFn(54);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action54::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant16(__nt), __end));
        (0, 26)
    }
    pub(crate) fn __reduce48<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // ActorTyp = "{", SepBy<MethTyp, ";">, "}" => ActionFn(43);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant17(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action43::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant17(__nt), __end));
        (3, 27)
    }
    pub(crate) fn __reduce49<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "bool" => ActionFn(3);
        let __sym0 = __pop_Variant1(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action3::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 28)
    }
    pub(crate) fn __reduce50<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "+", "number" => ActionFn(4);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant2(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action4::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (2, 28)
    }
    pub(crate) fn __reduce51<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "-", "number" => ActionFn(5);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant2(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action5::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (2, 28)
    }
    pub(crate) fn __reduce52<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "number" => ActionFn(6);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action6::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 28)
    }
    pub(crate) fn __reduce53<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "text" => ActionFn(7);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action7::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 28)
    }
    pub(crate) fn __reduce54<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "null" => ActionFn(8);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action8::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 28)
    }
    pub(crate) fn __reduce55<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "none" => ActionFn(9);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action9::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 28)
    }
    pub(crate) fn __reduce56<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "opt", Arg => ActionFn(10);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action10::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (2, 28)
    }
    pub(crate) fn __reduce57<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "vec", "{", SepBy<Arg, ";">, "}" => ActionFn(11);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant29(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action11::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (4, 28)
    }
    pub(crate) fn __reduce58<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "record", "{", SepBy<RecordField, ";">, "}" => ActionFn(12);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant32(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action12::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (4, 28)
    }
    pub(crate) fn __reduce59<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "variant", "{", VariantField, "}" => ActionFn(13);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant21(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action13::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (4, 28)
    }
    pub(crate) fn __reduce60<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg? = Arg => ActionFn(70);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action70::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant18(__nt), __end));
        (1, 29)
    }
    pub(crate) fn __reduce61<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg? =  => ActionFn(71);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action71::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant18(__nt), __end));
        (0, 29)
    }
    pub(crate) fn __reduce62<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // ArgTyp = Typ => ActionFn(39);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action39::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (1, 30)
    }
    pub(crate) fn __reduce63<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // ArgTyp = Name, ":", Typ => ActionFn(40);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant6(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action40::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (3, 30)
    }
    pub(crate) fn __reduce64<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // ArgTyp? = ArgTyp => ActionFn(90);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action90::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant16(__nt), __end));
        (1, 31)
    }
    pub(crate) fn __reduce65<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // ArgTyp? =  => ActionFn(91);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action91::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant16(__nt), __end));
        (0, 31)
    }
    pub(crate) fn __reduce66<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Args = "(", SepBy<Arg, ",">, ")" => ActionFn(2);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant29(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action2::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant19(__nt), __end));
        (3, 32)
    }
    pub(crate) fn __reduce67<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Def = "type", "id", "=", Typ => ActionFn(46);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant6(__symbols);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant2(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action46::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant8(__nt), __end));
        (4, 33)
    }
    pub(crate) fn __reduce68<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Def = "import", "text" => ActionFn(47);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant2(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action47::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant8(__nt), __end));
        (2, 33)
    }
    pub(crate) fn __reduce69<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Def? = Def => ActionFn(102);
        let __sym0 = __pop_Variant8(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action102::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant20(__nt), __end));
        (1, 34)
    }
    pub(crate) fn __reduce70<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Def? =  => ActionFn(103);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action103::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant20(__nt), __end));
        (0, 34)
    }
    pub(crate) fn __reduce71<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Field = "number", "=", Arg => ActionFn(14);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant4(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action14::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant21(__nt), __end));
        (3, 35)
    }
    pub(crate) fn __reduce72<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Field = Name, "=", Arg => ActionFn(15);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant4(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action15::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant21(__nt), __end));
        (3, 35)
    }
    pub(crate) fn __reduce73<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FieldTyp = "number", ":", Typ => ActionFn(31);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant6(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action31::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (3, 36)
    }
    pub(crate) fn __reduce74<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FieldTyp = Name, ":", Typ => ActionFn(32);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant6(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action32::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (3, 36)
    }
    pub(crate) fn __reduce75<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncMode = "oneway" => ActionFn(41);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action41::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant22(__nt), __end));
        (1, 37)
    }
    pub(crate) fn __reduce76<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncMode = "query" => ActionFn(42);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action42::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant22(__nt), __end));
        (1, 37)
    }
    pub(crate) fn __reduce77<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncMode* =  => ActionFn(59);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action59::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant23(__nt), __end));
        (0, 38)
    }
    pub(crate) fn __reduce78<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncMode* = FuncMode+ => ActionFn(60);
        let __sym0 = __pop_Variant23(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action60::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant23(__nt), __end));
        (1, 38)
    }
    pub(crate) fn __reduce79<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncMode+ = FuncMode => ActionFn(95);
        let __sym0 = __pop_Variant22(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action95::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant23(__nt), __end));
        (1, 39)
    }
    pub(crate) fn __reduce80<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncMode+ = FuncMode+, FuncMode => ActionFn(96);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant22(__symbols);
        let __sym0 = __pop_Variant23(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action96::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant23(__nt), __end));
        (2, 39)
    }
    pub(crate) fn __reduce81<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncTyp = "(", SepBy<ArgTyp, ",">, ")", "->", "(", SepBy<ArgTyp, ",">, ")" => ActionFn(177);
        assert!(__symbols.len() >= 7);
        let __sym6 = __pop_Variant0(__symbols);
        let __sym5 = __pop_Variant30(__symbols);
        let __sym4 = __pop_Variant0(__symbols);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant30(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym6.2.clone();
        let __nt = super::__action177::<>(__sym0, __sym1, __sym2, __sym3, __sym4, __sym5, __sym6);
        __symbols.push((__start, __Symbol::Variant24(__nt), __end));
        (7, 40)
    }
    pub(crate) fn __reduce82<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncTyp = "(", SepBy<ArgTyp, ",">, ")", "->", "(", SepBy<ArgTyp, ",">, ")", FuncMode+ => ActionFn(178);
        assert!(__symbols.len() >= 8);
        let __sym7 = __pop_Variant23(__symbols);
        let __sym6 = __pop_Variant0(__symbols);
        let __sym5 = __pop_Variant30(__symbols);
        let __sym4 = __pop_Variant0(__symbols);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant30(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym7.2.clone();
        let __nt = super::__action178::<>(__sym0, __sym1, __sym2, __sym3, __sym4, __sym5, __sym6, __sym7);
        __symbols.push((__start, __Symbol::Variant24(__nt), __end));
        (8, 40)
    }
    pub(crate) fn __reduce83<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // IDLProg = SepBy<Def, ";">, Actor => ActionFn(159);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant6(__symbols);
        let __sym0 = __pop_Variant31(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action159::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant25(__nt), __end));
        (2, 41)
    }
    pub(crate) fn __reduce84<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // IDLProg = SepBy<Def, ";"> => ActionFn(160);
        let __sym0 = __pop_Variant31(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action160::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant25(__nt), __end));
        (1, 41)
    }
    pub(crate) fn __reduce85<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // MethTyp = Name, ":", FuncTyp => ActionFn(44);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant24(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action44::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (3, 42)
    }
    pub(crate) fn __reduce86<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // MethTyp = Name, ":", "id" => ActionFn(45);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant2(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action45::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (3, 42)
    }
    pub(crate) fn __reduce87<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // MethTyp? = MethTyp => ActionFn(97);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action97::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant26(__nt), __end));
        (1, 43)
    }
    pub(crate) fn __reduce88<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // MethTyp? =  => ActionFn(98);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action98::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant26(__nt), __end));
        (0, 43)
    }
    pub(crate) fn __reduce89<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Name = "id" => ActionFn(51);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action51::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant2(__nt), __end));
        (1, 44)
    }
    pub(crate) fn __reduce90<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Name = "text" => ActionFn(52);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action52::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant2(__nt), __end));
        (1, 44)
    }
    pub(crate) fn __reduce91<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // PrimTyp = "null" => ActionFn(29);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action29::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (1, 45)
    }
    pub(crate) fn __reduce92<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // PrimTyp = "id" => ActionFn(30);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action30::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (1, 45)
    }
    pub(crate) fn __reduce93<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordField = Field => ActionFn(19);
        let __sym0 = __pop_Variant21(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action19::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant12(__nt), __end));
        (1, 46)
    }
    pub(crate) fn __reduce94<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordField = Arg => ActionFn(20);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action20::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant12(__nt), __end));
        (1, 46)
    }
    pub(crate) fn __reduce95<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordField? = RecordField => ActionFn(75);
        let __sym0 = __pop_Variant12(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action75::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant27(__nt), __end));
        (1, 47)
    }
    pub(crate) fn __reduce96<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordField? =  => ActionFn(76);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action76::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant27(__nt), __end));
        (0, 47)
    }
    pub(crate) fn __reduce97<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordFieldTyp = FieldTyp => ActionFn(33);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action33::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (1, 48)
    }
    pub(crate) fn __reduce98<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordFieldTyp = Typ => ActionFn(34);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action34::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (1, 48)
    }
    pub(crate) fn __reduce99<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordFieldTyp? = RecordFieldTyp => ActionFn(80);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action80::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant28(__nt), __end));
        (1, 49)
    }
    pub(crate) fn __reduce100<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordFieldTyp? =  => ActionFn(81);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action81::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant28(__nt), __end));
        (0, 49)
    }
    pub(crate) fn __reduce101<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ","> = Arg => ActionFn(161);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action161::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (1, 50)
    }
    pub(crate) fn __reduce102<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ","> =  => ActionFn(162);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action162::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (0, 50)
    }
    pub(crate) fn __reduce103<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ","> = (<Arg> ",")+, Arg => ActionFn(163);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action163::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (2, 50)
    }
    pub(crate) fn __reduce104<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ","> = (<Arg> ",")+ => ActionFn(164);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action164::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (1, 50)
    }
    pub(crate) fn __reduce105<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ";"> = Arg => ActionFn(165);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action165::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (1, 51)
    }
    pub(crate) fn __reduce106<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ";"> =  => ActionFn(166);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action166::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (0, 51)
    }
    pub(crate) fn __reduce107<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ";"> = (<Arg> ";")+, Arg => ActionFn(167);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action167::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (2, 51)
    }
    pub(crate) fn __reduce108<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ";"> = (<Arg> ";")+ => ActionFn(168);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action168::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (1, 51)
    }
    pub(crate) fn __reduce109<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<ArgTyp, ","> = ArgTyp => ActionFn(169);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action169::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant30(__nt), __end));
        (1, 52)
    }
    pub(crate) fn __reduce110<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<ArgTyp, ","> =  => ActionFn(170);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action170::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant30(__nt), __end));
        (0, 52)
    }
    pub(crate) fn __reduce111<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<ArgTyp, ","> = (<ArgTyp> ",")+, ArgTyp => ActionFn(171);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant6(__symbols);
        let __sym0 = __pop_Variant7(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action171::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant30(__nt), __end));
        (2, 52)
    }
    pub(crate) fn __reduce112<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<ArgTyp, ","> = (<ArgTyp> ",")+ => ActionFn(172);
        let __sym0 = __pop_Variant7(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action172::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant30(__nt), __end));
        (1, 52)
    }
    pub(crate) fn __reduce113<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Def, ";"> = Def => ActionFn(173);
        let __sym0 = __pop_Variant8(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action173::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant31(__nt), __end));
        (1, 53)
    }
    pub(crate) fn __reduce114<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Def, ";"> =  => ActionFn(174);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action174::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant31(__nt), __end));
        (0, 53)
    }
    pub(crate) fn __reduce115<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Def, ";"> = (<Def> ";")+, Def => ActionFn(175);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant8(__symbols);
        let __sym0 = __pop_Variant9(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action175::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant31(__nt), __end));
        (2, 53)
    }
    pub(crate) fn __reduce116<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Def, ";"> = (<Def> ";")+ => ActionFn(176);
        let __sym0 = __pop_Variant9(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action176::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant31(__nt), __end));
        (1, 53)
    }
    pub(crate) fn __reduce117<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<MethTyp, ";"> = MethTyp => ActionFn(179);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action179::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant17(__nt), __end));
        (1, 54)
    }
    pub(crate) fn __reduce118<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<MethTyp, ";"> =  => ActionFn(180);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action180::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant17(__nt), __end));
        (0, 54)
    }
    pub(crate) fn __reduce119<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<MethTyp, ";"> = (<MethTyp> ";")+, MethTyp => ActionFn(181);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant10(__symbols);
        let __sym0 = __pop_Variant11(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action181::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant17(__nt), __end));
        (2, 54)
    }
    pub(crate) fn __reduce120<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<MethTyp, ";"> = (<MethTyp> ";")+ => ActionFn(182);
        let __sym0 = __pop_Variant11(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action182::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant17(__nt), __end));
        (1, 54)
    }
    pub(crate) fn __reduce121<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordField, ";"> = RecordField => ActionFn(183);
        let __sym0 = __pop_Variant12(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action183::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant32(__nt), __end));
        (1, 55)
    }
    pub(crate) fn __reduce122<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordField, ";"> =  => ActionFn(184);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action184::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant32(__nt), __end));
        (0, 55)
    }
    pub(crate) fn __reduce123<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordField, ";"> = (<RecordField> ";")+, RecordField => ActionFn(185);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant12(__symbols);
        let __sym0 = __pop_Variant13(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action185::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant32(__nt), __end));
        (2, 55)
    }
    pub(crate) fn __reduce124<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordField, ";"> = (<RecordField> ";")+ => ActionFn(186);
        let __sym0 = __pop_Variant13(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action186::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant32(__nt), __end));
        (1, 55)
    }
    pub(crate) fn __reduce125<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordFieldTyp, ";"> = RecordFieldTyp => ActionFn(187);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action187::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (1, 56)
    }
    pub(crate) fn __reduce126<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordFieldTyp, ";"> =  => ActionFn(188);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action188::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (0, 56)
    }
    pub(crate) fn __reduce127<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordFieldTyp, ";"> = (<RecordFieldTyp> ";")+, RecordFieldTyp => ActionFn(189);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant14(__symbols);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action189::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (2, 56)
    }
    pub(crate) fn __reduce128<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordFieldTyp, ";"> = (<RecordFieldTyp> ";")+ => ActionFn(190);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action190::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (1, 56)
    }
    pub(crate) fn __reduce129<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<VariantFieldTyp, ";"> = VariantFieldTyp => ActionFn(191);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action191::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (1, 57)
    }
    pub(crate) fn __reduce130<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<VariantFieldTyp, ";"> =  => ActionFn(192);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action192::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (0, 57)
    }
    pub(crate) fn __reduce131<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<VariantFieldTyp, ";"> = (<VariantFieldTyp> ";")+, VariantFieldTyp => ActionFn(193);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant14(__symbols);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action193::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (2, 57)
    }
    pub(crate) fn __reduce132<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<VariantFieldTyp, ";"> = (<VariantFieldTyp> ";")+ => ActionFn(194);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action194::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (1, 57)
    }
    pub(crate) fn __reduce133<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = PrimTyp => ActionFn(21);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action21::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (1, 58)
    }
    pub(crate) fn __reduce134<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = "opt", Typ => ActionFn(22);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant6(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action22::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (2, 58)
    }
    pub(crate) fn __reduce135<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = "vec", Typ => ActionFn(23);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant6(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action23::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (2, 58)
    }
    pub(crate) fn __reduce136<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = "blob" => ActionFn(24);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action24::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (1, 58)
    }
    pub(crate) fn __reduce137<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = "record", "{", SepBy<RecordFieldTyp, ";">, "}" => ActionFn(25);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant33(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action25::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (4, 58)
    }
    pub(crate) fn __reduce138<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = "variant", "{", SepBy<VariantFieldTyp, ";">, "}" => ActionFn(26);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant33(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action26::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (4, 58)
    }
    pub(crate) fn __reduce139<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = "func", FuncTyp => ActionFn(27);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant24(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action27::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (2, 58)
    }
    pub(crate) fn __reduce140<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = "service", ActorTyp => ActionFn(28);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant17(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action28::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (2, 58)
    }
    pub(crate) fn __reduce141<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantField = Field => ActionFn(16);
        let __sym0 = __pop_Variant21(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action16::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant21(__nt), __end));
        (1, 59)
    }
    pub(crate) fn __reduce142<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantField = Name => ActionFn(17);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action17::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant21(__nt), __end));
        (1, 59)
    }
    pub(crate) fn __reduce143<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantField = "number" => ActionFn(18);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action18::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant21(__nt), __end));
        (1, 59)
    }
    pub(crate) fn __reduce144<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantFieldTyp = FieldTyp => ActionFn(35);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action35::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (1, 60)
    }
    pub(crate) fn __reduce145<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantFieldTyp = Name => ActionFn(36);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action36::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (1, 60)
    }
    pub(crate) fn __reduce146<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantFieldTyp = "number" => ActionFn(37);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action37::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (1, 60)
    }
    pub(crate) fn __reduce147<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantFieldTyp? = VariantFieldTyp => ActionFn(85);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action85::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant28(__nt), __end));
        (1, 61)
    }
    pub(crate) fn __reduce148<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantFieldTyp? =  => ActionFn(86);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action86::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant28(__nt), __end));
        (0, 61)
    }
    pub(crate) fn __reduce150<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // __IDLProg = IDLProg => ActionFn(1);
        let __sym0 = __pop_Variant25(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action1::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant25(__nt), __end));
        (1, 63)
    }
}
pub use self::__parse__Args::ArgsParser;

#[cfg_attr(rustfmt, rustfmt_skip)]
mod __parse__IDLProg {
    #![allow(non_snake_case, non_camel_case_types, unused_mut, unused_variables, unused_imports, unused_parens)]

    use super::super::value::{IDLField, IDLValue, IDLArgs};
    use super::super::types::{IDLType, PrimType, Label, TypeField, FuncType, FuncMode, Binding, Dec, IDLProg};
    use super::super::lexer::{Token, LexicalError, TmpIDLField};
    use crate::idl_hash;
    #[allow(unused_extern_crates)]
    extern crate lalrpop_util as __lalrpop_util;
    #[allow(unused_imports)]
    use self::__lalrpop_util::state_machine as __state_machine;
    use super::__ToTriple;
    #[allow(dead_code)]
    pub enum __Symbol<>
     {
        Variant0(Token),
        Variant1(bool),
        Variant2(String),
        Variant3(::std::option::Option<String>),
        Variant4(IDLValue),
        Variant5(::std::vec::Vec<IDLValue>),
        Variant6(IDLType),
        Variant7(::std::vec::Vec<IDLType>),
        Variant8(Dec),
        Variant9(::std::vec::Vec<Dec>),
        Variant10(Binding),
        Variant11(::std::vec::Vec<Binding>),
        Variant12(TmpIDLField),
        Variant13(::std::vec::Vec<TmpIDLField>),
        Variant14(TypeField),
        Variant15(::std::vec::Vec<TypeField>),
        Variant16(::std::option::Option<IDLType>),
        Variant17(Vec<Binding>),
        Variant18(::std::option::Option<IDLValue>),
        Variant19(IDLArgs),
        Variant20(::std::option::Option<Dec>),
        Variant21(IDLField),
        Variant22(FuncMode),
        Variant23(::std::vec::Vec<FuncMode>),
        Variant24(FuncType),
        Variant25(IDLProg),
        Variant26(::std::option::Option<Binding>),
        Variant27(::std::option::Option<TmpIDLField>),
        Variant28(::std::option::Option<TypeField>),
        Variant29(Vec<IDLValue>),
        Variant30(Vec<IDLType>),
        Variant31(Vec<Dec>),
        Variant32(Vec<TmpIDLField>),
        Variant33(Vec<TypeField>),
    }
    const __ACTION: &[i16] = &[
        // State 0
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, -115, 0, 29, 0, 0, 0, 0,
        // State 1
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, -117, 0, 29, 0, 0, 0, 0,
        // State 2
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0,
        // State 3
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0,
        // State 4
        0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 8, 43, 0, 0, 44, 0, 0, 9, 0, 45, 10, 0, 0, 46, 11, 0, 0,
        // State 5
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, -119,
        // State 6
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0,
        // State 7
        13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 8
        0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 8, 43, 0, 0, 44, 0, 0, 9, 0, 45, 10, 0, 0, 46, 11, 0, 0,
        // State 9
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0,
        // State 10
        0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 8, 43, 0, 0, 44, 0, 0, 9, 0, 45, 10, 0, 0, 46, 11, 0, 0,
        // State 11
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, -121,
        // State 12
        0, -111, 0, 0, 0, 0, 0, 0, 0, 42, 0, 8, 65, 0, 0, 44, 0, 0, 9, 0, 45, 10, 51, 0, 46, 11, 0, 0,
        // State 13
        0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 8, 65, 0, 0, 44, 71, 0, 9, 0, 45, 10, 51, 0, 46, 11, 0, -127,
        // State 14
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 0, 0, 0, 76, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, -131,
        // State 15
        13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 79, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 16
        0, -113, 0, 0, 0, 0, 0, 0, 0, 42, 0, 8, 65, 0, 0, 44, 0, 0, 9, 0, 45, 10, 51, 0, 46, 11, 0, 0,
        // State 17
        0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 8, 65, 0, 0, 44, 71, 0, 9, 0, 45, 10, 51, 0, 46, 11, 0, -129,
        // State 18
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 0, 0, 0, 76, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, -133,
        // State 19
        0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 8, 43, 0, 0, 44, 0, 0, 9, 0, 45, 10, 0, 0, 46, 11, 0, 0,
        // State 20
        0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 8, 43, 0, 0, 44, 0, 0, 9, 0, 45, 10, 0, 0, 46, 11, 0, 0,
        // State 21
        0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 8, 43, 0, 0, 44, 0, 0, 9, 0, 45, 10, 0, 0, 46, 11, 0, 0,
        // State 22
        0, -111, 0, 0, 0, 0, 0, 0, 0, 42, 0, 8, 65, 0, 0, 44, 0, 0, 9, 0, 45, 10, 51, 0, 46, 11, 0, 0,
        // State 23
        0, -82, 0, -82, 0, 0, 0, -82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 98, 0, 99, 0, -82, 0, 0, 0, 0, 0, -82,
        // State 24
        0, -83, 0, -83, 0, 0, 0, -83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 98, 0, 99, 0, -83, 0, 0, 0, 0, 0, -83,
        // State 25
        0, 0, 0, 0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -114, 0, 0, 0, 0, 0, 0,
        // State 26
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 27
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0,
        // State 28
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 29
        0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -116, 0, 0, 0, 0, 0, 0,
        // State 30
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -21, 0, 0, 0, 0, 0, 0, 0, -21, 0, -21, 0, 0, 0, 0,
        // State 31
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 32
        0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 33
        0, 0, 0, 0, 0, 0, 0, -69, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -69, 0, 0, 0, 0, 0, 0,
        // State 34
        0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 35
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -22, 0, 0, 0, 0, 0, 0, 0, -22, 0, -22, 0, 0, 0, 0,
        // State 36
        0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 37
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 38
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 39
        0, -134, 0, -134, 0, 0, 0, -134, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -134, 0, 0, 0, 0, 0, -134,
        // State 40
        0, 0, 0, 0, 0, 0, 0, -68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -68, 0, 0, 0, 0, 0, 0,
        // State 41
        0, -137, 0, -137, 0, 0, 0, -137, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -137, 0, 0, 0, 0, 0, -137,
        // State 42
        0, -93, 0, -93, 0, 0, 0, -93, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -93, 0, 0, 0, 0, 0, -93,
        // State 43
        0, -92, 0, -92, 0, 0, 0, -92, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -92, 0, 0, 0, 0, 0, -92,
        // State 44
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0,
        // State 45
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0,
        // State 46
        0, 0, 0, 0, 0, 0, 0, 59, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -118,
        // State 47
        0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 48
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60,
        // State 49
        0, 0, 0, 0, 0, 0, -90, -90, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -90,
        // State 50
        0, 0, 0, 0, 0, 0, -91, -91, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -91,
        // State 51
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 52
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 53
        0, -140, 0, -140, 0, 0, 0, -140, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -140, 0, 0, 0, 0, 0, -140,
        // State 54
        0, -135, 0, -135, 0, 0, 0, -135, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -135, 0, 0, 0, 0, 0, -135,
        // State 55
        0, -141, 0, -141, 0, 0, 0, -141, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -141, 0, 0, 0, 0, 0, -141,
        // State 56
        0, -136, 0, -136, 0, 0, 0, -136, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -136, 0, 0, 0, 0, 0, -136,
        // State 57
        0, 0, 0, 0, 0, 0, 0, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -120,
        // State 58
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -26, 0, 0, 0, 0, 0, 0, 0, 0, 0, -26, 0, 0, 0, 0, -26,
        // State 59
        0, -49, 0, -49, 0, 0, 0, -49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -49, 0, 0, 0, 0, 0, -49,
        // State 60
        0, -110, 0, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 61
        0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 62
        0, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 63
        0, -63, 0, -63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 64
        0, -93, 0, -93, 0, 0, -90, -93, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -93,
        // State 65
        0, 0, 0, 0, 0, 0, 0, -98, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -98,
        // State 66
        0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 67
        0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -126,
        // State 68
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85,
        // State 69
        0, 0, 0, 0, 0, 0, 0, -99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -99,
        // State 70
        0, 0, 0, 0, 0, 0, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 71
        0, 0, 0, 0, 0, 0, 0, -145, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -145,
        // State 72
        0, 0, 0, 0, 0, 0, 21, -146, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -146,
        // State 73
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 87,
        // State 74
        0, 0, 0, 0, 0, 0, 0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -130,
        // State 75
        0, 0, 0, 0, 0, 0, 22, -147, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -147,
        // State 76
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -27, 0, 0, 0, 0, 0, 0, 0, 0, 0, -27, 0, 0, 0, 0, -27,
        // State 77
        0, 0, 0, 0, 0, 0, 0, -86, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -86,
        // State 78
        0, 0, 0, 0, 0, 0, 0, -87, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -87,
        // State 79
        0, -112, 0, 89, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 80
        0, -16, 0, 0, 0, 0, 0, 0, 0, -16, 0, -16, -16, 0, 0, -16, 0, 0, -16, 0, -16, -16, -16, 0, -16, -16, 0, 0,
        // State 81
        0, 0, 0, 0, 0, 91, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 82
        0, 0, 0, 0, 0, 0, 0, 92, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -128,
        // State 83
        0, 0, 0, 0, 0, 0, 0, 0, 0, -36, 0, -36, -36, 0, 0, -36, -36, 0, -36, 0, -36, -36, -36, 0, -36, -36, 0, -36,
        // State 84
        0, -138, 0, -138, 0, 0, 0, -138, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -138, 0, 0, 0, 0, 0, -138,
        // State 85
        0, 0, 0, 0, 0, 0, 0, 95, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -132,
        // State 86
        0, -139, 0, -139, 0, 0, 0, -139, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -139, 0, 0, 0, 0, 0, -139,
        // State 87
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -41, 0, 0, 0, -41, 0, 0, 0, 0, 0, -41, 0, 0, 0, 0, -41,
        // State 88
        0, -17, 0, 0, 0, 0, 0, 0, 0, -17, 0, -17, -17, 0, 0, -17, 0, 0, -17, 0, -17, -17, -17, 0, -17, -17, 0, 0,
        // State 89
        0, -64, 0, -64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 90
        23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 91
        0, 0, 0, 0, 0, 0, 0, 0, 0, -37, 0, -37, -37, 0, 0, -37, -37, 0, -37, 0, -37, -37, -37, 0, -37, -37, 0, -37,
        // State 92
        0, 0, 0, 0, 0, 0, 0, -75, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -75,
        // State 93
        0, 0, 0, 0, 0, 0, 0, -74, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -74,
        // State 94
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -42, 0, 0, 0, -42, 0, 0, 0, 0, 0, -42, 0, 0, 0, 0, -42,
        // State 95
        0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        // State 96
        0, -80, 0, -80, 0, 0, 0, -80, 0, 0, 0, 0, 0, 0, 0, 0, 0, -80, 0, -80, 0, -80, 0, 0, 0, 0, 0, -80,
        // State 97
        0, -76, 0, -76, 0, 0, 0, -76, 0, 0, 0, 0, 0, 0, 0, 0, 0, -76, 0, -76, 0, -76, 0, 0, 0, 0, 0, -76,
        // State 98
        0, -77, 0, -77, 0, 0, 0, -77, 0, 0, 0, 0, 0, 0, 0, 0, 0, -77, 0, -77, 0, -77, 0, 0, 0, 0, 0, -77,
        // State 99
        0, -81, 0, -81, 0, 0, 0, -81, 0, 0, 0, 0, 0, 0, 0, 0, 0, -81, 0, -81, 0, -81, 0, 0, 0, 0, 0, -81,
    ];
    fn __action(state: i16, integer: usize) -> i16 {
        __ACTION[(state as usize) * 28 + integer]
    }
    const __EOF_ACTION: &[i16] = &[
        // State 0
        -115,
        // State 1
        -117,
        // State 2
        -85,
        // State 3
        0,
        // State 4
        0,
        // State 5
        0,
        // State 6
        0,
        // State 7
        0,
        // State 8
        0,
        // State 9
        0,
        // State 10
        0,
        // State 11
        0,
        // State 12
        0,
        // State 13
        0,
        // State 14
        0,
        // State 15
        0,
        // State 16
        0,
        // State 17
        0,
        // State 18
        0,
        // State 19
        0,
        // State 20
        0,
        // State 21
        0,
        // State 22
        0,
        // State 23
        -82,
        // State 24
        -83,
        // State 25
        -114,
        // State 26
        -151,
        // State 27
        0,
        // State 28
        0,
        // State 29
        -116,
        // State 30
        -21,
        // State 31
        -84,
        // State 32
        0,
        // State 33
        -69,
        // State 34
        0,
        // State 35
        -22,
        // State 36
        0,
        // State 37
        -44,
        // State 38
        -46,
        // State 39
        -134,
        // State 40
        -68,
        // State 41
        -137,
        // State 42
        -93,
        // State 43
        -92,
        // State 44
        0,
        // State 45
        0,
        // State 46
        0,
        // State 47
        0,
        // State 48
        0,
        // State 49
        0,
        // State 50
        0,
        // State 51
        -43,
        // State 52
        -45,
        // State 53
        -140,
        // State 54
        -135,
        // State 55
        -141,
        // State 56
        -136,
        // State 57
        0,
        // State 58
        0,
        // State 59
        -49,
        // State 60
        0,
        // State 61
        0,
        // State 62
        0,
        // State 63
        0,
        // State 64
        0,
        // State 65
        0,
        // State 66
        0,
        // State 67
        0,
        // State 68
        0,
        // State 69
        0,
        // State 70
        0,
        // State 71
        0,
        // State 72
        0,
        // State 73
        0,
        // State 74
        0,
        // State 75
        0,
        // State 76
        0,
        // State 77
        0,
        // State 78
        0,
        // State 79
        0,
        // State 80
        0,
        // State 81
        0,
        // State 82
        0,
        // State 83
        0,
        // State 84
        -138,
        // State 85
        0,
        // State 86
        -139,
        // State 87
        0,
        // State 88
        0,
        // State 89
        0,
        // State 90
        0,
        // State 91
        0,
        // State 92
        0,
        // State 93
        0,
        // State 94
        0,
        // State 95
        0,
        // State 96
        -80,
        // State 97
        -76,
        // State 98
        -77,
        // State 99
        -81,
    ];
    fn __goto(state: i16, nt: usize) -> i16 {
        match nt {
            9 => 16,
            12 => 1,
            15 => 11,
            21 => 17,
            24 => 18,
            25 => 31,
            27 => match state {
                6 => 51,
                9 => 55,
                _ => 37,
            },
            30 => match state {
                16 => 79,
                _ => 60,
            },
            33 => match state {
                1 => 29,
                _ => 25,
            },
            36 => match state {
                14 | 18 => 71,
                _ => 65,
            },
            37 => match state {
                24 => 99,
                _ => 96,
            },
            39 => 24,
            40 => match state {
                15 => 77,
                _ => 53,
            },
            41 => 26,
            42 => match state {
                11 => 57,
                _ => 46,
            },
            44 => match state {
                5 | 11 => 47,
                13 | 17 => 66,
                14 | 18 => 72,
                _ => 61,
            },
            45 => 39,
            48 => match state {
                17 => 82,
                _ => 67,
            },
            52 => match state {
                22 => 95,
                _ => 62,
            },
            53 => 2,
            54 => 48,
            56 => 68,
            57 => 73,
            58 => match state {
                4 => 40,
                8 => 54,
                10 => 56,
                13 | 17 => 69,
                19 => 89,
                20 => 92,
                21 => 93,
                _ => 63,
            },
            60 => match state {
                18 => 85,
                _ => 74,
            },
            _ => 0,
        }
    }
    fn __expected_tokens(__state: i16) -> Vec<::std::string::String> {
        const __TERMINAL: &[&str] = &[
            r###""(""###,
            r###"")""###,
            r###""+""###,
            r###"",""###,
            r###""-""###,
            r###""->""###,
            r###"":""###,
            r###"";""###,
            r###""=""###,
            r###""blob""###,
            r###""bool""###,
            r###""func""###,
            r###""id""###,
            r###""import""###,
            r###""none""###,
            r###""null""###,
            r###""number""###,
            r###""oneway""###,
            r###""opt""###,
            r###""query""###,
            r###""record""###,
            r###""service""###,
            r###""text""###,
            r###""type""###,
            r###""variant""###,
            r###""vec""###,
            r###""{""###,
            r###""}""###,
        ];
        __TERMINAL.iter().enumerate().filter_map(|(index, terminal)| {
            let next_state = __action(__state, index);
            if next_state == 0 {
                None
            } else {
                Some(terminal.to_string())
            }
        }).collect()
    }
    pub struct __StateMachine<>
    where 
    {
        __phantom: ::std::marker::PhantomData<()>,
    }
    impl<> __state_machine::ParserDefinition for __StateMachine<>
    where 
    {
        type Location = usize;
        type Error = LexicalError;
        type Token = Token;
        type TokenIndex = usize;
        type Symbol = __Symbol<>;
        type Success = IDLProg;
        type StateIndex = i16;
        type Action = i16;
        type ReduceIndex = i16;
        type NonterminalIndex = usize;

        #[inline]
        fn start_location(&self) -> Self::Location {
              Default::default()
        }

        #[inline]
        fn start_state(&self) -> Self::StateIndex {
              0
        }

        #[inline]
        fn token_to_index(&self, token: &Self::Token) -> Option<usize> {
            __token_to_integer(token, ::std::marker::PhantomData::<()>)
        }

        #[inline]
        fn action(&self, state: i16, integer: usize) -> i16 {
            __action(state, integer)
        }

        #[inline]
        fn error_action(&self, state: i16) -> i16 {
            __action(state, 28 - 1)
        }

        #[inline]
        fn eof_action(&self, state: i16) -> i16 {
            __EOF_ACTION[state as usize]
        }

        #[inline]
        fn goto(&self, state: i16, nt: usize) -> i16 {
            __goto(state, nt)
        }

        fn token_to_symbol(&self, token_index: usize, token: Self::Token) -> Self::Symbol {
            __token_to_symbol(token_index, token, ::std::marker::PhantomData::<()>)
        }

        fn expected_tokens(&self, state: i16) -> Vec<String> {
            __expected_tokens(state)
        }

        #[inline]
        fn uses_error_recovery(&self) -> bool {
            false
        }

        #[inline]
        fn error_recovery_symbol(
            &self,
            recovery: __state_machine::ErrorRecovery<Self>,
        ) -> Self::Symbol {
            panic!("error recovery not enabled for this grammar")
        }

        fn reduce(
            &mut self,
            action: i16,
            start_location: Option<&Self::Location>,
            states: &mut Vec<i16>,
            symbols: &mut Vec<__state_machine::SymbolTriple<Self>>,
        ) -> Option<__state_machine::ParseResult<Self>> {
            __reduce(
                action,
                start_location,
                states,
                symbols,
                ::std::marker::PhantomData::<()>,
            )
        }

        fn simulate_reduce(&self, action: i16) -> __state_machine::SimulatedReduce<Self> {
            panic!("error recovery not enabled for this grammar")
        }
    }
    fn __token_to_integer<
    >(
        __token: &Token,
        _: ::std::marker::PhantomData<()>,
    ) -> Option<usize>
    {
        match *__token {
            Token::LParen if true => Some(0),
            Token::RParen if true => Some(1),
            Token::Plus if true => Some(2),
            Token::Comma if true => Some(3),
            Token::Minus if true => Some(4),
            Token::Arrow if true => Some(5),
            Token::Colon if true => Some(6),
            Token::Semi if true => Some(7),
            Token::Equals if true => Some(8),
            Token::Blob if true => Some(9),
            Token::Boolean(_) if true => Some(10),
            Token::Func if true => Some(11),
            Token::Id(_) if true => Some(12),
            Token::Import if true => Some(13),
            Token::None if true => Some(14),
            Token::Null if true => Some(15),
            Token::Number(_) if true => Some(16),
            Token::Oneway if true => Some(17),
            Token::Opt if true => Some(18),
            Token::Query if true => Some(19),
            Token::Record if true => Some(20),
            Token::Service if true => Some(21),
            Token::Text(_) if true => Some(22),
            Token::Type if true => Some(23),
            Token::Variant if true => Some(24),
            Token::Vec if true => Some(25),
            Token::LBrace if true => Some(26),
            Token::RBrace if true => Some(27),
            _ => None,
        }
    }
    fn __token_to_symbol<
    >(
        __token_index: usize,
        __token: Token,
        _: ::std::marker::PhantomData<()>,
    ) -> __Symbol<>
    {
        match __token_index {
            0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 11 | 13 | 14 | 15 | 17 | 18 | 19 | 20 | 21 | 23 | 24 | 25 | 26 | 27 => __Symbol::Variant0(__token),
            10 => match __token {
                Token::Boolean(__tok0) if true => __Symbol::Variant1(__tok0),
                _ => unreachable!(),
            },
            12 | 16 | 22 => match __token {
                Token::Id(__tok0) | Token::Number(__tok0) | Token::Text(__tok0) if true => __Symbol::Variant2(__tok0),
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }
    pub struct IDLProgParser {
        _priv: (),
    }

    impl IDLProgParser {
        pub fn new() -> IDLProgParser {
            IDLProgParser {
                _priv: (),
            }
        }

        #[allow(dead_code)]
        pub fn parse<
            __TOKEN: __ToTriple<>,
            __TOKENS: IntoIterator<Item=__TOKEN>,
        >(
            &self,
            __tokens0: __TOKENS,
        ) -> Result<IDLProg, __lalrpop_util::ParseError<usize, Token, LexicalError>>
        {
            let __tokens = __tokens0.into_iter();
            let mut __tokens = __tokens.map(|t| __ToTriple::to_triple(t));
            __state_machine::Parser::drive(
                __StateMachine {
                    __phantom: ::std::marker::PhantomData::<()>,
                },
                __tokens,
            )
        }
    }
    pub(crate) fn __reduce<
    >(
        __action: i16,
        __lookahead_start: Option<&usize>,
        __states: &mut ::std::vec::Vec<i16>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> Option<Result<IDLProg,__lalrpop_util::ParseError<usize, Token, LexicalError>>>
    {
        let (__pop_states, __nonterminal) = match __action {
            0 => {
                __reduce0(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            1 => {
                __reduce1(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            2 => {
                __reduce2(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            3 => {
                __reduce3(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            4 => {
                __reduce4(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            5 => {
                __reduce5(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            6 => {
                __reduce6(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            7 => {
                __reduce7(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            8 => {
                __reduce8(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            9 => {
                __reduce9(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            10 => {
                __reduce10(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            11 => {
                __reduce11(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            12 => {
                __reduce12(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            13 => {
                __reduce13(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            14 => {
                __reduce14(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            15 => {
                __reduce15(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            16 => {
                __reduce16(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            17 => {
                __reduce17(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            18 => {
                __reduce18(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            19 => {
                __reduce19(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            20 => {
                __reduce20(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            21 => {
                __reduce21(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            22 => {
                __reduce22(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            23 => {
                __reduce23(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            24 => {
                __reduce24(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            25 => {
                __reduce25(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            26 => {
                __reduce26(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            27 => {
                __reduce27(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            28 => {
                __reduce28(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            29 => {
                __reduce29(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            30 => {
                __reduce30(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            31 => {
                __reduce31(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            32 => {
                __reduce32(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            33 => {
                __reduce33(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            34 => {
                __reduce34(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            35 => {
                __reduce35(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            36 => {
                __reduce36(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            37 => {
                __reduce37(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            38 => {
                __reduce38(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            39 => {
                __reduce39(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            40 => {
                __reduce40(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            41 => {
                __reduce41(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            42 => {
                __reduce42(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            43 => {
                __reduce43(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            44 => {
                __reduce44(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            45 => {
                __reduce45(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            46 => {
                __reduce46(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            47 => {
                __reduce47(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            48 => {
                __reduce48(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            49 => {
                __reduce49(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            50 => {
                __reduce50(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            51 => {
                __reduce51(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            52 => {
                __reduce52(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            53 => {
                __reduce53(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            54 => {
                __reduce54(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            55 => {
                __reduce55(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            56 => {
                __reduce56(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            57 => {
                __reduce57(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            58 => {
                __reduce58(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            59 => {
                __reduce59(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            60 => {
                __reduce60(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            61 => {
                __reduce61(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            62 => {
                __reduce62(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            63 => {
                __reduce63(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            64 => {
                __reduce64(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            65 => {
                __reduce65(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            66 => {
                __reduce66(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            67 => {
                __reduce67(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            68 => {
                __reduce68(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            69 => {
                __reduce69(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            70 => {
                __reduce70(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            71 => {
                __reduce71(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            72 => {
                __reduce72(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            73 => {
                __reduce73(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            74 => {
                __reduce74(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            75 => {
                __reduce75(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            76 => {
                __reduce76(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            77 => {
                __reduce77(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            78 => {
                __reduce78(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            79 => {
                __reduce79(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            80 => {
                __reduce80(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            81 => {
                __reduce81(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            82 => {
                __reduce82(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            83 => {
                __reduce83(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            84 => {
                __reduce84(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            85 => {
                __reduce85(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            86 => {
                __reduce86(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            87 => {
                __reduce87(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            88 => {
                __reduce88(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            89 => {
                __reduce89(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            90 => {
                __reduce90(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            91 => {
                __reduce91(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            92 => {
                __reduce92(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            93 => {
                __reduce93(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            94 => {
                __reduce94(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            95 => {
                __reduce95(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            96 => {
                __reduce96(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            97 => {
                __reduce97(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            98 => {
                __reduce98(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            99 => {
                __reduce99(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            100 => {
                __reduce100(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            101 => {
                __reduce101(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            102 => {
                __reduce102(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            103 => {
                __reduce103(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            104 => {
                __reduce104(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            105 => {
                __reduce105(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            106 => {
                __reduce106(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            107 => {
                __reduce107(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            108 => {
                __reduce108(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            109 => {
                __reduce109(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            110 => {
                __reduce110(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            111 => {
                __reduce111(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            112 => {
                __reduce112(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            113 => {
                __reduce113(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            114 => {
                __reduce114(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            115 => {
                __reduce115(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            116 => {
                __reduce116(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            117 => {
                __reduce117(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            118 => {
                __reduce118(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            119 => {
                __reduce119(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            120 => {
                __reduce120(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            121 => {
                __reduce121(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            122 => {
                __reduce122(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            123 => {
                __reduce123(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            124 => {
                __reduce124(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            125 => {
                __reduce125(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            126 => {
                __reduce126(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            127 => {
                __reduce127(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            128 => {
                __reduce128(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            129 => {
                __reduce129(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            130 => {
                __reduce130(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            131 => {
                __reduce131(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            132 => {
                __reduce132(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            133 => {
                __reduce133(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            134 => {
                __reduce134(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            135 => {
                __reduce135(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            136 => {
                __reduce136(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            137 => {
                __reduce137(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            138 => {
                __reduce138(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            139 => {
                __reduce139(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            140 => {
                __reduce140(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            141 => {
                __reduce141(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            142 => {
                __reduce142(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            143 => {
                __reduce143(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            144 => {
                __reduce144(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            145 => {
                __reduce145(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            146 => {
                __reduce146(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            147 => {
                __reduce147(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            148 => {
                __reduce148(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            149 => {
                __reduce149(__lookahead_start, __symbols, ::std::marker::PhantomData::<()>)
            }
            150 => {
                // __IDLProg = IDLProg => ActionFn(1);
                let __sym0 = __pop_Variant25(__symbols);
                let __start = __sym0.0.clone();
                let __end = __sym0.2.clone();
                let __nt = super::__action1::<>(__sym0);
                return Some(Ok(__nt));
            }
            _ => panic!("invalid action code {}", __action)
        };
        let __states_len = __states.len();
        __states.truncate(__states_len - __pop_states);
        let __state = *__states.last().unwrap();
        let __next_state = __goto(__state, __nonterminal);
        __states.push(__next_state);
        None
    }
    #[inline(never)]
    fn __symbol_type_mismatch() -> ! {
        panic!("symbol type mismatch")
    }
    fn __pop_Variant10<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Binding, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant10(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant8<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Dec, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant8(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant22<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, FuncMode, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant22(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant24<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, FuncType, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant24(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant19<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, IDLArgs, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant19(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant21<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, IDLField, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant21(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant25<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, IDLProg, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant25(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant6<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, IDLType, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant6(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant4<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, IDLValue, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant4(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant2<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, String, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant2(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant12<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, TmpIDLField, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant12(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant0<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Token, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant0(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant14<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, TypeField, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant14(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant17<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Vec<Binding>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant17(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant31<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Vec<Dec>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant31(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant30<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Vec<IDLType>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant30(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant29<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Vec<IDLValue>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant29(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant32<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Vec<TmpIDLField>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant32(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant33<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, Vec<TypeField>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant33(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant1<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, bool, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant1(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant26<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::option::Option<Binding>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant26(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant20<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::option::Option<Dec>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant20(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant16<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::option::Option<IDLType>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant16(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant18<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::option::Option<IDLValue>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant18(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant3<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::option::Option<String>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant3(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant27<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::option::Option<TmpIDLField>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant27(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant28<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::option::Option<TypeField>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant28(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant11<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::vec::Vec<Binding>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant11(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant9<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::vec::Vec<Dec>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant9(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant23<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::vec::Vec<FuncMode>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant23(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant7<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::vec::Vec<IDLType>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant7(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant5<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::vec::Vec<IDLValue>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant5(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant13<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::vec::Vec<TmpIDLField>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant13(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    fn __pop_Variant15<
    >(
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>
    ) -> (usize, ::std::vec::Vec<TypeField>, usize)
     {
        match __symbols.pop().unwrap() {
            (__l, __Symbol::Variant15(__v), __r) => (__l, __v, __r),
            _ => __symbol_type_mismatch()
        }
    }
    pub(crate) fn __reduce0<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // "id"? = "id" => ActionFn(56);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action56::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant3(__nt), __end));
        (1, 0)
    }
    pub(crate) fn __reduce1<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // "id"? =  => ActionFn(57);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action57::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant3(__nt), __end));
        (0, 0)
    }
    pub(crate) fn __reduce2<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ",") = Arg, "," => ActionFn(69);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action69::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (2, 1)
    }
    pub(crate) fn __reduce3<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ",")* =  => ActionFn(67);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action67::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (0, 2)
    }
    pub(crate) fn __reduce4<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ",")* = (<Arg> ",")+ => ActionFn(68);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action68::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 2)
    }
    pub(crate) fn __reduce5<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ",")+ = Arg, "," => ActionFn(127);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action127::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (2, 3)
    }
    pub(crate) fn __reduce6<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ",")+ = (<Arg> ",")+, Arg, "," => ActionFn(128);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action128::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 3)
    }
    pub(crate) fn __reduce7<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ";") = Arg, ";" => ActionFn(74);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action74::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (2, 4)
    }
    pub(crate) fn __reduce8<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ";")* =  => ActionFn(72);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action72::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (0, 5)
    }
    pub(crate) fn __reduce9<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ";")* = (<Arg> ";")+ => ActionFn(73);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action73::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (1, 5)
    }
    pub(crate) fn __reduce10<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ";")+ = Arg, ";" => ActionFn(131);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action131::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (2, 6)
    }
    pub(crate) fn __reduce11<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Arg> ";")+ = (<Arg> ";")+, Arg, ";" => ActionFn(132);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action132::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant5(__nt), __end));
        (3, 6)
    }
    pub(crate) fn __reduce12<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<ArgTyp> ",") = ArgTyp, "," => ActionFn(94);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action94::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (2, 7)
    }
    pub(crate) fn __reduce13<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<ArgTyp> ",")* =  => ActionFn(92);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action92::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant7(__nt), __end));
        (0, 8)
    }
    pub(crate) fn __reduce14<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<ArgTyp> ",")* = (<ArgTyp> ",")+ => ActionFn(93);
        let __sym0 = __pop_Variant7(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action93::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant7(__nt), __end));
        (1, 8)
    }
    pub(crate) fn __reduce15<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<ArgTyp> ",")+ = ArgTyp, "," => ActionFn(135);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action135::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant7(__nt), __end));
        (2, 9)
    }
    pub(crate) fn __reduce16<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<ArgTyp> ",")+ = (<ArgTyp> ",")+, ArgTyp, "," => ActionFn(136);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant6(__symbols);
        let __sym0 = __pop_Variant7(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action136::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant7(__nt), __end));
        (3, 9)
    }
    pub(crate) fn __reduce17<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Def> ";") = Def, ";" => ActionFn(106);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant8(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action106::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant8(__nt), __end));
        (2, 10)
    }
    pub(crate) fn __reduce18<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Def> ";")* =  => ActionFn(104);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action104::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant9(__nt), __end));
        (0, 11)
    }
    pub(crate) fn __reduce19<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Def> ";")* = (<Def> ";")+ => ActionFn(105);
        let __sym0 = __pop_Variant9(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action105::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant9(__nt), __end));
        (1, 11)
    }
    pub(crate) fn __reduce20<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Def> ";")+ = Def, ";" => ActionFn(139);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant8(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action139::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant9(__nt), __end));
        (2, 12)
    }
    pub(crate) fn __reduce21<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<Def> ";")+ = (<Def> ";")+, Def, ";" => ActionFn(140);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant8(__symbols);
        let __sym0 = __pop_Variant9(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action140::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant9(__nt), __end));
        (3, 12)
    }
    pub(crate) fn __reduce22<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<MethTyp> ";") = MethTyp, ";" => ActionFn(101);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action101::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (2, 13)
    }
    pub(crate) fn __reduce23<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<MethTyp> ";")* =  => ActionFn(99);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action99::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant11(__nt), __end));
        (0, 14)
    }
    pub(crate) fn __reduce24<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<MethTyp> ";")* = (<MethTyp> ";")+ => ActionFn(100);
        let __sym0 = __pop_Variant11(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action100::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant11(__nt), __end));
        (1, 14)
    }
    pub(crate) fn __reduce25<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<MethTyp> ";")+ = MethTyp, ";" => ActionFn(143);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action143::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant11(__nt), __end));
        (2, 15)
    }
    pub(crate) fn __reduce26<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<MethTyp> ";")+ = (<MethTyp> ";")+, MethTyp, ";" => ActionFn(144);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant10(__symbols);
        let __sym0 = __pop_Variant11(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action144::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant11(__nt), __end));
        (3, 15)
    }
    pub(crate) fn __reduce27<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordField> ";") = RecordField, ";" => ActionFn(79);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant12(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action79::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant12(__nt), __end));
        (2, 16)
    }
    pub(crate) fn __reduce28<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordField> ";")* =  => ActionFn(77);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action77::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant13(__nt), __end));
        (0, 17)
    }
    pub(crate) fn __reduce29<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordField> ";")* = (<RecordField> ";")+ => ActionFn(78);
        let __sym0 = __pop_Variant13(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action78::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant13(__nt), __end));
        (1, 17)
    }
    pub(crate) fn __reduce30<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordField> ";")+ = RecordField, ";" => ActionFn(147);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant12(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action147::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant13(__nt), __end));
        (2, 18)
    }
    pub(crate) fn __reduce31<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordField> ";")+ = (<RecordField> ";")+, RecordField, ";" => ActionFn(148);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant12(__symbols);
        let __sym0 = __pop_Variant13(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action148::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant13(__nt), __end));
        (3, 18)
    }
    pub(crate) fn __reduce32<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordFieldTyp> ";") = RecordFieldTyp, ";" => ActionFn(84);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action84::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (2, 19)
    }
    pub(crate) fn __reduce33<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordFieldTyp> ";")* =  => ActionFn(82);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action82::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (0, 20)
    }
    pub(crate) fn __reduce34<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordFieldTyp> ";")* = (<RecordFieldTyp> ";")+ => ActionFn(83);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action83::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (1, 20)
    }
    pub(crate) fn __reduce35<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordFieldTyp> ";")+ = RecordFieldTyp, ";" => ActionFn(151);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action151::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (2, 21)
    }
    pub(crate) fn __reduce36<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<RecordFieldTyp> ";")+ = (<RecordFieldTyp> ";")+, RecordFieldTyp, ";" => ActionFn(152);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant14(__symbols);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action152::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (3, 21)
    }
    pub(crate) fn __reduce37<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<VariantFieldTyp> ";") = VariantFieldTyp, ";" => ActionFn(89);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action89::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (2, 22)
    }
    pub(crate) fn __reduce38<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<VariantFieldTyp> ";")* =  => ActionFn(87);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action87::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (0, 23)
    }
    pub(crate) fn __reduce39<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<VariantFieldTyp> ";")* = (<VariantFieldTyp> ";")+ => ActionFn(88);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action88::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (1, 23)
    }
    pub(crate) fn __reduce40<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<VariantFieldTyp> ";")+ = VariantFieldTyp, ";" => ActionFn(155);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action155::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (2, 24)
    }
    pub(crate) fn __reduce41<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // (<VariantFieldTyp> ";")+ = (<VariantFieldTyp> ";")+, VariantFieldTyp, ";" => ActionFn(156);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant14(__symbols);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action156::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant15(__nt), __end));
        (3, 24)
    }
    pub(crate) fn __reduce42<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Actor = "service", "id", ":", ActorTyp => ActionFn(123);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant17(__symbols);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant2(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action123::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (4, 25)
    }
    pub(crate) fn __reduce43<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Actor = "service", ":", ActorTyp => ActionFn(124);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant17(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action124::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (3, 25)
    }
    pub(crate) fn __reduce44<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Actor = "service", "id", ":", "id" => ActionFn(125);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant2(__symbols);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant2(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action125::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (4, 25)
    }
    pub(crate) fn __reduce45<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Actor = "service", ":", "id" => ActionFn(126);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant2(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action126::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (3, 25)
    }
    pub(crate) fn __reduce46<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Actor? = Actor => ActionFn(53);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action53::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant16(__nt), __end));
        (1, 26)
    }
    pub(crate) fn __reduce47<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Actor? =  => ActionFn(54);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action54::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant16(__nt), __end));
        (0, 26)
    }
    pub(crate) fn __reduce48<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // ActorTyp = "{", SepBy<MethTyp, ";">, "}" => ActionFn(43);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant17(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action43::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant17(__nt), __end));
        (3, 27)
    }
    pub(crate) fn __reduce49<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "bool" => ActionFn(3);
        let __sym0 = __pop_Variant1(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action3::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 28)
    }
    pub(crate) fn __reduce50<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "+", "number" => ActionFn(4);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant2(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action4::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (2, 28)
    }
    pub(crate) fn __reduce51<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "-", "number" => ActionFn(5);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant2(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action5::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (2, 28)
    }
    pub(crate) fn __reduce52<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "number" => ActionFn(6);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action6::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 28)
    }
    pub(crate) fn __reduce53<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "text" => ActionFn(7);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action7::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 28)
    }
    pub(crate) fn __reduce54<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "null" => ActionFn(8);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action8::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 28)
    }
    pub(crate) fn __reduce55<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "none" => ActionFn(9);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action9::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (1, 28)
    }
    pub(crate) fn __reduce56<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "opt", Arg => ActionFn(10);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action10::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (2, 28)
    }
    pub(crate) fn __reduce57<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "vec", "{", SepBy<Arg, ";">, "}" => ActionFn(11);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant29(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action11::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (4, 28)
    }
    pub(crate) fn __reduce58<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "record", "{", SepBy<RecordField, ";">, "}" => ActionFn(12);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant32(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action12::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (4, 28)
    }
    pub(crate) fn __reduce59<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg = "variant", "{", VariantField, "}" => ActionFn(13);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant21(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action13::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant4(__nt), __end));
        (4, 28)
    }
    pub(crate) fn __reduce60<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg? = Arg => ActionFn(70);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action70::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant18(__nt), __end));
        (1, 29)
    }
    pub(crate) fn __reduce61<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Arg? =  => ActionFn(71);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action71::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant18(__nt), __end));
        (0, 29)
    }
    pub(crate) fn __reduce62<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // ArgTyp = Typ => ActionFn(39);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action39::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (1, 30)
    }
    pub(crate) fn __reduce63<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // ArgTyp = Name, ":", Typ => ActionFn(40);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant6(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action40::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (3, 30)
    }
    pub(crate) fn __reduce64<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // ArgTyp? = ArgTyp => ActionFn(90);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action90::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant16(__nt), __end));
        (1, 31)
    }
    pub(crate) fn __reduce65<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // ArgTyp? =  => ActionFn(91);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action91::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant16(__nt), __end));
        (0, 31)
    }
    pub(crate) fn __reduce66<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Args = "(", SepBy<Arg, ",">, ")" => ActionFn(2);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant29(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action2::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant19(__nt), __end));
        (3, 32)
    }
    pub(crate) fn __reduce67<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Def = "type", "id", "=", Typ => ActionFn(46);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant6(__symbols);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant2(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action46::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant8(__nt), __end));
        (4, 33)
    }
    pub(crate) fn __reduce68<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Def = "import", "text" => ActionFn(47);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant2(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action47::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant8(__nt), __end));
        (2, 33)
    }
    pub(crate) fn __reduce69<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Def? = Def => ActionFn(102);
        let __sym0 = __pop_Variant8(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action102::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant20(__nt), __end));
        (1, 34)
    }
    pub(crate) fn __reduce70<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Def? =  => ActionFn(103);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action103::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant20(__nt), __end));
        (0, 34)
    }
    pub(crate) fn __reduce71<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Field = "number", "=", Arg => ActionFn(14);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant4(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action14::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant21(__nt), __end));
        (3, 35)
    }
    pub(crate) fn __reduce72<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Field = Name, "=", Arg => ActionFn(15);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant4(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action15::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant21(__nt), __end));
        (3, 35)
    }
    pub(crate) fn __reduce73<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FieldTyp = "number", ":", Typ => ActionFn(31);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant6(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action31::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (3, 36)
    }
    pub(crate) fn __reduce74<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FieldTyp = Name, ":", Typ => ActionFn(32);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant6(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action32::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (3, 36)
    }
    pub(crate) fn __reduce75<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncMode = "oneway" => ActionFn(41);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action41::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant22(__nt), __end));
        (1, 37)
    }
    pub(crate) fn __reduce76<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncMode = "query" => ActionFn(42);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action42::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant22(__nt), __end));
        (1, 37)
    }
    pub(crate) fn __reduce77<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncMode* =  => ActionFn(59);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action59::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant23(__nt), __end));
        (0, 38)
    }
    pub(crate) fn __reduce78<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncMode* = FuncMode+ => ActionFn(60);
        let __sym0 = __pop_Variant23(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action60::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant23(__nt), __end));
        (1, 38)
    }
    pub(crate) fn __reduce79<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncMode+ = FuncMode => ActionFn(95);
        let __sym0 = __pop_Variant22(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action95::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant23(__nt), __end));
        (1, 39)
    }
    pub(crate) fn __reduce80<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncMode+ = FuncMode+, FuncMode => ActionFn(96);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant22(__symbols);
        let __sym0 = __pop_Variant23(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action96::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant23(__nt), __end));
        (2, 39)
    }
    pub(crate) fn __reduce81<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncTyp = "(", SepBy<ArgTyp, ",">, ")", "->", "(", SepBy<ArgTyp, ",">, ")" => ActionFn(177);
        assert!(__symbols.len() >= 7);
        let __sym6 = __pop_Variant0(__symbols);
        let __sym5 = __pop_Variant30(__symbols);
        let __sym4 = __pop_Variant0(__symbols);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant30(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym6.2.clone();
        let __nt = super::__action177::<>(__sym0, __sym1, __sym2, __sym3, __sym4, __sym5, __sym6);
        __symbols.push((__start, __Symbol::Variant24(__nt), __end));
        (7, 40)
    }
    pub(crate) fn __reduce82<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // FuncTyp = "(", SepBy<ArgTyp, ",">, ")", "->", "(", SepBy<ArgTyp, ",">, ")", FuncMode+ => ActionFn(178);
        assert!(__symbols.len() >= 8);
        let __sym7 = __pop_Variant23(__symbols);
        let __sym6 = __pop_Variant0(__symbols);
        let __sym5 = __pop_Variant30(__symbols);
        let __sym4 = __pop_Variant0(__symbols);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant0(__symbols);
        let __sym1 = __pop_Variant30(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym7.2.clone();
        let __nt = super::__action178::<>(__sym0, __sym1, __sym2, __sym3, __sym4, __sym5, __sym6, __sym7);
        __symbols.push((__start, __Symbol::Variant24(__nt), __end));
        (8, 40)
    }
    pub(crate) fn __reduce83<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // IDLProg = SepBy<Def, ";">, Actor => ActionFn(159);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant6(__symbols);
        let __sym0 = __pop_Variant31(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action159::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant25(__nt), __end));
        (2, 41)
    }
    pub(crate) fn __reduce84<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // IDLProg = SepBy<Def, ";"> => ActionFn(160);
        let __sym0 = __pop_Variant31(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action160::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant25(__nt), __end));
        (1, 41)
    }
    pub(crate) fn __reduce85<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // MethTyp = Name, ":", FuncTyp => ActionFn(44);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant24(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action44::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (3, 42)
    }
    pub(crate) fn __reduce86<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // MethTyp = Name, ":", "id" => ActionFn(45);
        assert!(__symbols.len() >= 3);
        let __sym2 = __pop_Variant2(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym2.2.clone();
        let __nt = super::__action45::<>(__sym0, __sym1, __sym2);
        __symbols.push((__start, __Symbol::Variant10(__nt), __end));
        (3, 42)
    }
    pub(crate) fn __reduce87<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // MethTyp? = MethTyp => ActionFn(97);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action97::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant26(__nt), __end));
        (1, 43)
    }
    pub(crate) fn __reduce88<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // MethTyp? =  => ActionFn(98);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action98::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant26(__nt), __end));
        (0, 43)
    }
    pub(crate) fn __reduce89<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Name = "id" => ActionFn(51);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action51::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant2(__nt), __end));
        (1, 44)
    }
    pub(crate) fn __reduce90<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Name = "text" => ActionFn(52);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action52::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant2(__nt), __end));
        (1, 44)
    }
    pub(crate) fn __reduce91<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // PrimTyp = "null" => ActionFn(29);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action29::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (1, 45)
    }
    pub(crate) fn __reduce92<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // PrimTyp = "id" => ActionFn(30);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action30::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (1, 45)
    }
    pub(crate) fn __reduce93<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordField = Field => ActionFn(19);
        let __sym0 = __pop_Variant21(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action19::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant12(__nt), __end));
        (1, 46)
    }
    pub(crate) fn __reduce94<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordField = Arg => ActionFn(20);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action20::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant12(__nt), __end));
        (1, 46)
    }
    pub(crate) fn __reduce95<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordField? = RecordField => ActionFn(75);
        let __sym0 = __pop_Variant12(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action75::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant27(__nt), __end));
        (1, 47)
    }
    pub(crate) fn __reduce96<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordField? =  => ActionFn(76);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action76::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant27(__nt), __end));
        (0, 47)
    }
    pub(crate) fn __reduce97<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordFieldTyp = FieldTyp => ActionFn(33);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action33::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (1, 48)
    }
    pub(crate) fn __reduce98<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordFieldTyp = Typ => ActionFn(34);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action34::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (1, 48)
    }
    pub(crate) fn __reduce99<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordFieldTyp? = RecordFieldTyp => ActionFn(80);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action80::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant28(__nt), __end));
        (1, 49)
    }
    pub(crate) fn __reduce100<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // RecordFieldTyp? =  => ActionFn(81);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action81::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant28(__nt), __end));
        (0, 49)
    }
    pub(crate) fn __reduce101<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ","> = Arg => ActionFn(161);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action161::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (1, 50)
    }
    pub(crate) fn __reduce102<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ","> =  => ActionFn(162);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action162::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (0, 50)
    }
    pub(crate) fn __reduce103<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ","> = (<Arg> ",")+, Arg => ActionFn(163);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action163::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (2, 50)
    }
    pub(crate) fn __reduce104<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ","> = (<Arg> ",")+ => ActionFn(164);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action164::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (1, 50)
    }
    pub(crate) fn __reduce105<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ";"> = Arg => ActionFn(165);
        let __sym0 = __pop_Variant4(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action165::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (1, 51)
    }
    pub(crate) fn __reduce106<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ";"> =  => ActionFn(166);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action166::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (0, 51)
    }
    pub(crate) fn __reduce107<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ";"> = (<Arg> ";")+, Arg => ActionFn(167);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant4(__symbols);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action167::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (2, 51)
    }
    pub(crate) fn __reduce108<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Arg, ";"> = (<Arg> ";")+ => ActionFn(168);
        let __sym0 = __pop_Variant5(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action168::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant29(__nt), __end));
        (1, 51)
    }
    pub(crate) fn __reduce109<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<ArgTyp, ","> = ArgTyp => ActionFn(169);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action169::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant30(__nt), __end));
        (1, 52)
    }
    pub(crate) fn __reduce110<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<ArgTyp, ","> =  => ActionFn(170);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action170::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant30(__nt), __end));
        (0, 52)
    }
    pub(crate) fn __reduce111<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<ArgTyp, ","> = (<ArgTyp> ",")+, ArgTyp => ActionFn(171);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant6(__symbols);
        let __sym0 = __pop_Variant7(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action171::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant30(__nt), __end));
        (2, 52)
    }
    pub(crate) fn __reduce112<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<ArgTyp, ","> = (<ArgTyp> ",")+ => ActionFn(172);
        let __sym0 = __pop_Variant7(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action172::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant30(__nt), __end));
        (1, 52)
    }
    pub(crate) fn __reduce113<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Def, ";"> = Def => ActionFn(173);
        let __sym0 = __pop_Variant8(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action173::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant31(__nt), __end));
        (1, 53)
    }
    pub(crate) fn __reduce114<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Def, ";"> =  => ActionFn(174);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action174::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant31(__nt), __end));
        (0, 53)
    }
    pub(crate) fn __reduce115<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Def, ";"> = (<Def> ";")+, Def => ActionFn(175);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant8(__symbols);
        let __sym0 = __pop_Variant9(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action175::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant31(__nt), __end));
        (2, 53)
    }
    pub(crate) fn __reduce116<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<Def, ";"> = (<Def> ";")+ => ActionFn(176);
        let __sym0 = __pop_Variant9(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action176::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant31(__nt), __end));
        (1, 53)
    }
    pub(crate) fn __reduce117<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<MethTyp, ";"> = MethTyp => ActionFn(179);
        let __sym0 = __pop_Variant10(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action179::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant17(__nt), __end));
        (1, 54)
    }
    pub(crate) fn __reduce118<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<MethTyp, ";"> =  => ActionFn(180);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action180::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant17(__nt), __end));
        (0, 54)
    }
    pub(crate) fn __reduce119<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<MethTyp, ";"> = (<MethTyp> ";")+, MethTyp => ActionFn(181);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant10(__symbols);
        let __sym0 = __pop_Variant11(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action181::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant17(__nt), __end));
        (2, 54)
    }
    pub(crate) fn __reduce120<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<MethTyp, ";"> = (<MethTyp> ";")+ => ActionFn(182);
        let __sym0 = __pop_Variant11(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action182::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant17(__nt), __end));
        (1, 54)
    }
    pub(crate) fn __reduce121<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordField, ";"> = RecordField => ActionFn(183);
        let __sym0 = __pop_Variant12(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action183::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant32(__nt), __end));
        (1, 55)
    }
    pub(crate) fn __reduce122<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordField, ";"> =  => ActionFn(184);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action184::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant32(__nt), __end));
        (0, 55)
    }
    pub(crate) fn __reduce123<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordField, ";"> = (<RecordField> ";")+, RecordField => ActionFn(185);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant12(__symbols);
        let __sym0 = __pop_Variant13(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action185::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant32(__nt), __end));
        (2, 55)
    }
    pub(crate) fn __reduce124<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordField, ";"> = (<RecordField> ";")+ => ActionFn(186);
        let __sym0 = __pop_Variant13(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action186::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant32(__nt), __end));
        (1, 55)
    }
    pub(crate) fn __reduce125<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordFieldTyp, ";"> = RecordFieldTyp => ActionFn(187);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action187::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (1, 56)
    }
    pub(crate) fn __reduce126<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordFieldTyp, ";"> =  => ActionFn(188);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action188::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (0, 56)
    }
    pub(crate) fn __reduce127<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordFieldTyp, ";"> = (<RecordFieldTyp> ";")+, RecordFieldTyp => ActionFn(189);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant14(__symbols);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action189::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (2, 56)
    }
    pub(crate) fn __reduce128<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<RecordFieldTyp, ";"> = (<RecordFieldTyp> ";")+ => ActionFn(190);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action190::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (1, 56)
    }
    pub(crate) fn __reduce129<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<VariantFieldTyp, ";"> = VariantFieldTyp => ActionFn(191);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action191::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (1, 57)
    }
    pub(crate) fn __reduce130<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<VariantFieldTyp, ";"> =  => ActionFn(192);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action192::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (0, 57)
    }
    pub(crate) fn __reduce131<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<VariantFieldTyp, ";"> = (<VariantFieldTyp> ";")+, VariantFieldTyp => ActionFn(193);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant14(__symbols);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action193::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (2, 57)
    }
    pub(crate) fn __reduce132<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // SepBy<VariantFieldTyp, ";"> = (<VariantFieldTyp> ";")+ => ActionFn(194);
        let __sym0 = __pop_Variant15(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action194::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant33(__nt), __end));
        (1, 57)
    }
    pub(crate) fn __reduce133<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = PrimTyp => ActionFn(21);
        let __sym0 = __pop_Variant6(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action21::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (1, 58)
    }
    pub(crate) fn __reduce134<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = "opt", Typ => ActionFn(22);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant6(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action22::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (2, 58)
    }
    pub(crate) fn __reduce135<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = "vec", Typ => ActionFn(23);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant6(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action23::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (2, 58)
    }
    pub(crate) fn __reduce136<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = "blob" => ActionFn(24);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action24::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (1, 58)
    }
    pub(crate) fn __reduce137<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = "record", "{", SepBy<RecordFieldTyp, ";">, "}" => ActionFn(25);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant33(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action25::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (4, 58)
    }
    pub(crate) fn __reduce138<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = "variant", "{", SepBy<VariantFieldTyp, ";">, "}" => ActionFn(26);
        assert!(__symbols.len() >= 4);
        let __sym3 = __pop_Variant0(__symbols);
        let __sym2 = __pop_Variant33(__symbols);
        let __sym1 = __pop_Variant0(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym3.2.clone();
        let __nt = super::__action26::<>(__sym0, __sym1, __sym2, __sym3);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (4, 58)
    }
    pub(crate) fn __reduce139<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = "func", FuncTyp => ActionFn(27);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant24(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action27::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (2, 58)
    }
    pub(crate) fn __reduce140<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // Typ = "service", ActorTyp => ActionFn(28);
        assert!(__symbols.len() >= 2);
        let __sym1 = __pop_Variant17(__symbols);
        let __sym0 = __pop_Variant0(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym1.2.clone();
        let __nt = super::__action28::<>(__sym0, __sym1);
        __symbols.push((__start, __Symbol::Variant6(__nt), __end));
        (2, 58)
    }
    pub(crate) fn __reduce141<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantField = Field => ActionFn(16);
        let __sym0 = __pop_Variant21(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action16::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant21(__nt), __end));
        (1, 59)
    }
    pub(crate) fn __reduce142<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantField = Name => ActionFn(17);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action17::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant21(__nt), __end));
        (1, 59)
    }
    pub(crate) fn __reduce143<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantField = "number" => ActionFn(18);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action18::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant21(__nt), __end));
        (1, 59)
    }
    pub(crate) fn __reduce144<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantFieldTyp = FieldTyp => ActionFn(35);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action35::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (1, 60)
    }
    pub(crate) fn __reduce145<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantFieldTyp = Name => ActionFn(36);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action36::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (1, 60)
    }
    pub(crate) fn __reduce146<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantFieldTyp = "number" => ActionFn(37);
        let __sym0 = __pop_Variant2(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action37::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant14(__nt), __end));
        (1, 60)
    }
    pub(crate) fn __reduce147<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantFieldTyp? = VariantFieldTyp => ActionFn(85);
        let __sym0 = __pop_Variant14(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action85::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant28(__nt), __end));
        (1, 61)
    }
    pub(crate) fn __reduce148<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // VariantFieldTyp? =  => ActionFn(86);
        let __start = __lookahead_start.cloned().or_else(|| __symbols.last().map(|s| s.2.clone())).unwrap_or_default();
        let __end = __start.clone();
        let __nt = super::__action86::<>(&__start, &__end);
        __symbols.push((__start, __Symbol::Variant28(__nt), __end));
        (0, 61)
    }
    pub(crate) fn __reduce149<
    >(
        __lookahead_start: Option<&usize>,
        __symbols: &mut ::std::vec::Vec<(usize,__Symbol<>,usize)>,
        _: ::std::marker::PhantomData<()>,
    ) -> (usize, usize)
    {
        // __Args = Args => ActionFn(0);
        let __sym0 = __pop_Variant19(__symbols);
        let __start = __sym0.0.clone();
        let __end = __sym0.2.clone();
        let __nt = super::__action0::<>(__sym0);
        __symbols.push((__start, __Symbol::Variant19(__nt), __end));
        (1, 62)
    }
}
pub use self::__parse__IDLProg::IDLProgParser;

fn __action0<
>(
    (_, __0, _): (usize, IDLArgs, usize),
) -> IDLArgs
{
    __0
}

fn __action1<
>(
    (_, __0, _): (usize, IDLProg, usize),
) -> IDLProg
{
    __0
}

fn __action2<
>(
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, Vec<IDLValue>, usize),
    (_, _, _): (usize, Token, usize),
) -> IDLArgs
{
    IDLArgs { args: __0 }
}

fn __action3<
>(
    (_, __0, _): (usize, bool, usize),
) -> IDLValue
{
    IDLValue::Bool(__0)
}

fn __action4<
>(
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, String, usize),
) -> IDLValue
{
    IDLValue::Int(__0.parse::<i64>().unwrap())
}

fn __action5<
>(
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, String, usize),
) -> IDLValue
{
    IDLValue::Int(format!("-{}", __0).parse::<i64>().unwrap())
}

fn __action6<
>(
    (_, __0, _): (usize, String, usize),
) -> IDLValue
{
    IDLValue::Nat(__0.parse::<u64>().unwrap())
}

fn __action7<
>(
    (_, __0, _): (usize, String, usize),
) -> IDLValue
{
    IDLValue::Text(__0)
}

fn __action8<
>(
    (_, __0, _): (usize, Token, usize),
) -> IDLValue
{
    IDLValue::Null
}

fn __action9<
>(
    (_, __0, _): (usize, Token, usize),
) -> IDLValue
{
    IDLValue::None
}

fn __action10<
>(
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, IDLValue, usize),
) -> IDLValue
{
    IDLValue::Opt(Box::new(__0))
}

fn __action11<
>(
    (_, _, _): (usize, Token, usize),
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, Vec<IDLValue>, usize),
    (_, _, _): (usize, Token, usize),
) -> IDLValue
{
    IDLValue::Vec(__0)
}

fn __action12<
>(
    (_, _, _): (usize, Token, usize),
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, Vec<TmpIDLField>, usize),
    (_, _, _): (usize, Token, usize),
) -> IDLValue
{
    {
        let mut id: u32 = 0;
        let mut fs: Vec<IDLField> = __0.iter().map(|f| {
          if f.has_id {
            id = f.inner.id + 1;
            f.inner.clone()
          } else {
            id = id + 1;
            IDLField { id: id - 1, val: f.inner.val.clone() }
          }
        }).collect();
        fs.sort_unstable_by_key(|IDLField { id, .. }| *id);
        IDLValue::Record(fs)
     }
}

fn __action13<
>(
    (_, _, _): (usize, Token, usize),
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, IDLField, usize),
    (_, _, _): (usize, Token, usize),
) -> IDLValue
{
    IDLValue::Variant(Box::new(__0))
}

fn __action14<
>(
    (_, n, _): (usize, String, usize),
    (_, _, _): (usize, Token, usize),
    (_, v, _): (usize, IDLValue, usize),
) -> IDLField
{
    IDLField { id: n.parse::<u32>().unwrap(), val: v }
}

fn __action15<
>(
    (_, n, _): (usize, String, usize),
    (_, _, _): (usize, Token, usize),
    (_, v, _): (usize, IDLValue, usize),
) -> IDLField
{
    IDLField { id: idl_hash(&n), val: v }
}

fn __action16<
>(
    (_, __0, _): (usize, IDLField, usize),
) -> IDLField
{
    __0
}

fn __action17<
>(
    (_, __0, _): (usize, String, usize),
) -> IDLField
{
    IDLField { id: idl_hash(&__0), val: IDLValue::Null }
}

fn __action18<
>(
    (_, __0, _): (usize, String, usize),
) -> IDLField
{
    IDLField { id: __0.parse::<u32>().unwrap(), val: IDLValue::Null }
}

fn __action19<
>(
    (_, __0, _): (usize, IDLField, usize),
) -> TmpIDLField
{
    TmpIDLField { has_id: true, inner: __0 }
}

fn __action20<
>(
    (_, __0, _): (usize, IDLValue, usize),
) -> TmpIDLField
{
    TmpIDLField { has_id: false, inner: IDLField { id:0, val:__0 } }
}

fn __action21<
>(
    (_, __0, _): (usize, IDLType, usize),
) -> IDLType
{
    __0
}

fn __action22<
>(
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, IDLType, usize),
) -> IDLType
{
    IDLType::OptT(Box::new(__0))
}

fn __action23<
>(
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, IDLType, usize),
) -> IDLType
{
    IDLType::VecT(Box::new(__0))
}

fn __action24<
>(
    (_, __0, _): (usize, Token, usize),
) -> IDLType
{
    IDLType::VecT(Box::new(IDLType::PrimT(PrimType::Nat8)))
}

fn __action25<
>(
    (_, _, _): (usize, Token, usize),
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, Vec<TypeField>, usize),
    (_, _, _): (usize, Token, usize),
) -> IDLType
{
    {
        let mut id: u32 = 0;
        let mut fs: Vec<TypeField> = __0.iter().map(|f| {
          let label = match f.label {
              Label::Unnamed(_) => { id = id + 1; Label::Unnamed(id - 1) },
              ref l => { id = l.get_id() + 1; l.clone() },
          };
          TypeField { label, typ: f.typ.clone() }
        }).collect();
        fs.sort_unstable_by_key(|TypeField { label, .. }| label.get_id());
        IDLType::RecordT(fs)
    }
}

fn __action26<
>(
    (_, _, _): (usize, Token, usize),
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, Vec<TypeField>, usize),
    (_, _, _): (usize, Token, usize),
) -> IDLType
{
    {
        let mut fs = __0;
        fs.sort_unstable_by_key(|TypeField { label, .. }| label.get_id());
        IDLType::VariantT(fs)
    }
}

fn __action27<
>(
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, FuncType, usize),
) -> IDLType
{
    IDLType::FuncT(__0)
}

fn __action28<
>(
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, Vec<Binding>, usize),
) -> IDLType
{
    IDLType::ServT(__0)
}

fn __action29<
>(
    (_, __0, _): (usize, Token, usize),
) -> IDLType
{
    IDLType::PrimT(PrimType::Null)
}

fn __action30<
>(
    (_, __0, _): (usize, String, usize),
) -> IDLType
{
    {
      match PrimType::str_to_enum(&__0) {
        Some(p) => IDLType::PrimT(p),
        None => IDLType::VarT(__0),
      }
    }
}

fn __action31<
>(
    (_, n, _): (usize, String, usize),
    (_, _, _): (usize, Token, usize),
    (_, t, _): (usize, IDLType, usize),
) -> TypeField
{
    TypeField { label: Label::Id(n.parse::<u32>().unwrap()), typ: t }
}

fn __action32<
>(
    (_, n, _): (usize, String, usize),
    (_, _, _): (usize, Token, usize),
    (_, t, _): (usize, IDLType, usize),
) -> TypeField
{
    TypeField { label: Label::Named(n), typ: t }
}

fn __action33<
>(
    (_, __0, _): (usize, TypeField, usize),
) -> TypeField
{
    __0
}

fn __action34<
>(
    (_, __0, _): (usize, IDLType, usize),
) -> TypeField
{
    TypeField { label: Label::Unnamed(0), typ: __0 }
}

fn __action35<
>(
    (_, __0, _): (usize, TypeField, usize),
) -> TypeField
{
    __0
}

fn __action36<
>(
    (_, __0, _): (usize, String, usize),
) -> TypeField
{
    TypeField { label: Label::Named(__0), typ: IDLType::PrimT(PrimType::Null) }
}

fn __action37<
>(
    (_, __0, _): (usize, String, usize),
) -> TypeField
{
    TypeField { label: Label::Id(__0.parse::<u32>().unwrap()), typ: IDLType::PrimT(PrimType::Null) }
}

fn __action38<
>(
    (_, _, _): (usize, Token, usize),
    (_, args, _): (usize, Vec<IDLType>, usize),
    (_, _, _): (usize, Token, usize),
    (_, _, _): (usize, Token, usize),
    (_, _, _): (usize, Token, usize),
    (_, rets, _): (usize, Vec<IDLType>, usize),
    (_, _, _): (usize, Token, usize),
    (_, modes, _): (usize, ::std::vec::Vec<FuncMode>, usize),
) -> FuncType
{
    FuncType { modes, args, rets }
}

fn __action39<
>(
    (_, __0, _): (usize, IDLType, usize),
) -> IDLType
{
    __0
}

fn __action40<
>(
    (_, _, _): (usize, String, usize),
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, IDLType, usize),
) -> IDLType
{
    __0
}

fn __action41<
>(
    (_, __0, _): (usize, Token, usize),
) -> FuncMode
{
    FuncMode::Oneway
}

fn __action42<
>(
    (_, __0, _): (usize, Token, usize),
) -> FuncMode
{
    FuncMode::Query
}

fn __action43<
>(
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, Vec<Binding>, usize),
    (_, _, _): (usize, Token, usize),
) -> Vec<Binding>
{
    __0
}

fn __action44<
>(
    (_, n, _): (usize, String, usize),
    (_, _, _): (usize, Token, usize),
    (_, f, _): (usize, FuncType, usize),
) -> Binding
{
    Binding { id: n, typ: IDLType::FuncT(f) }
}

fn __action45<
>(
    (_, n, _): (usize, String, usize),
    (_, _, _): (usize, Token, usize),
    (_, id, _): (usize, String, usize),
) -> Binding
{
    Binding { id: n, typ: IDLType::VarT(id) }
}

fn __action46<
>(
    (_, _, _): (usize, Token, usize),
    (_, id, _): (usize, String, usize),
    (_, _, _): (usize, Token, usize),
    (_, t, _): (usize, IDLType, usize),
) -> Dec
{
    Dec::TypD(Binding { id: id, typ: t })
}

fn __action47<
>(
    (_, _, _): (usize, Token, usize),
    (_, __0, _): (usize, String, usize),
) -> Dec
{
    Dec::ImportD(__0)
}

fn __action48<
>(
    (_, _, _): (usize, Token, usize),
    (_, _, _): (usize, ::std::option::Option<String>, usize),
    (_, _, _): (usize, Token, usize),
    (_, t, _): (usize, Vec<Binding>, usize),
) -> IDLType
{
    IDLType::ServT(t)
}

fn __action49<
>(
    (_, _, _): (usize, Token, usize),
    (_, _, _): (usize, ::std::option::Option<String>, usize),
    (_, _, _): (usize, Token, usize),
    (_, t, _): (usize, String, usize),
) -> IDLType
{
    IDLType::VarT(t)
}

fn __action50<
>(
    (_, decs, _): (usize, Vec<Dec>, usize),
    (_, actor, _): (usize, ::std::option::Option<IDLType>, usize),
) -> IDLProg
{
    IDLProg { decs, actor }
}

fn __action51<
>(
    (_, __0, _): (usize, String, usize),
) -> String
{
    __0
}

fn __action52<
>(
    (_, __0, _): (usize, String, usize),
) -> String
{
    __0
}

fn __action53<
>(
    (_, __0, _): (usize, IDLType, usize),
) -> ::std::option::Option<IDLType>
{
    Some(__0)
}

fn __action54<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::option::Option<IDLType>
{
    None
}

fn __action55<
>(
    (_, v, _): (usize, ::std::vec::Vec<Dec>, usize),
    (_, e, _): (usize, ::std::option::Option<Dec>, usize),
) -> Vec<Dec>
{
    match e {
        None => v,
        Some(e) => {
            let mut v = v;
            v.push(e);
            v
        }
    }
}

fn __action56<
>(
    (_, __0, _): (usize, String, usize),
) -> ::std::option::Option<String>
{
    Some(__0)
}

fn __action57<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::option::Option<String>
{
    None
}

fn __action58<
>(
    (_, v, _): (usize, ::std::vec::Vec<Binding>, usize),
    (_, e, _): (usize, ::std::option::Option<Binding>, usize),
) -> Vec<Binding>
{
    match e {
        None => v,
        Some(e) => {
            let mut v = v;
            v.push(e);
            v
        }
    }
}

fn __action59<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::vec::Vec<FuncMode>
{
    vec![]
}

fn __action60<
>(
    (_, v, _): (usize, ::std::vec::Vec<FuncMode>, usize),
) -> ::std::vec::Vec<FuncMode>
{
    v
}

fn __action61<
>(
    (_, v, _): (usize, ::std::vec::Vec<IDLType>, usize),
    (_, e, _): (usize, ::std::option::Option<IDLType>, usize),
) -> Vec<IDLType>
{
    match e {
        None => v,
        Some(e) => {
            let mut v = v;
            v.push(e);
            v
        }
    }
}

fn __action62<
>(
    (_, v, _): (usize, ::std::vec::Vec<TypeField>, usize),
    (_, e, _): (usize, ::std::option::Option<TypeField>, usize),
) -> Vec<TypeField>
{
    match e {
        None => v,
        Some(e) => {
            let mut v = v;
            v.push(e);
            v
        }
    }
}

fn __action63<
>(
    (_, v, _): (usize, ::std::vec::Vec<TypeField>, usize),
    (_, e, _): (usize, ::std::option::Option<TypeField>, usize),
) -> Vec<TypeField>
{
    match e {
        None => v,
        Some(e) => {
            let mut v = v;
            v.push(e);
            v
        }
    }
}

fn __action64<
>(
    (_, v, _): (usize, ::std::vec::Vec<TmpIDLField>, usize),
    (_, e, _): (usize, ::std::option::Option<TmpIDLField>, usize),
) -> Vec<TmpIDLField>
{
    match e {
        None => v,
        Some(e) => {
            let mut v = v;
            v.push(e);
            v
        }
    }
}

fn __action65<
>(
    (_, v, _): (usize, ::std::vec::Vec<IDLValue>, usize),
    (_, e, _): (usize, ::std::option::Option<IDLValue>, usize),
) -> Vec<IDLValue>
{
    match e {
        None => v,
        Some(e) => {
            let mut v = v;
            v.push(e);
            v
        }
    }
}

fn __action66<
>(
    (_, v, _): (usize, ::std::vec::Vec<IDLValue>, usize),
    (_, e, _): (usize, ::std::option::Option<IDLValue>, usize),
) -> Vec<IDLValue>
{
    match e {
        None => v,
        Some(e) => {
            let mut v = v;
            v.push(e);
            v
        }
    }
}

fn __action67<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::vec::Vec<IDLValue>
{
    vec![]
}

fn __action68<
>(
    (_, v, _): (usize, ::std::vec::Vec<IDLValue>, usize),
) -> ::std::vec::Vec<IDLValue>
{
    v
}

fn __action69<
>(
    (_, __0, _): (usize, IDLValue, usize),
    (_, _, _): (usize, Token, usize),
) -> IDLValue
{
    __0
}

fn __action70<
>(
    (_, __0, _): (usize, IDLValue, usize),
) -> ::std::option::Option<IDLValue>
{
    Some(__0)
}

fn __action71<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::option::Option<IDLValue>
{
    None
}

fn __action72<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::vec::Vec<IDLValue>
{
    vec![]
}

fn __action73<
>(
    (_, v, _): (usize, ::std::vec::Vec<IDLValue>, usize),
) -> ::std::vec::Vec<IDLValue>
{
    v
}

fn __action74<
>(
    (_, __0, _): (usize, IDLValue, usize),
    (_, _, _): (usize, Token, usize),
) -> IDLValue
{
    __0
}

fn __action75<
>(
    (_, __0, _): (usize, TmpIDLField, usize),
) -> ::std::option::Option<TmpIDLField>
{
    Some(__0)
}

fn __action76<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::option::Option<TmpIDLField>
{
    None
}

fn __action77<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::vec::Vec<TmpIDLField>
{
    vec![]
}

fn __action78<
>(
    (_, v, _): (usize, ::std::vec::Vec<TmpIDLField>, usize),
) -> ::std::vec::Vec<TmpIDLField>
{
    v
}

fn __action79<
>(
    (_, __0, _): (usize, TmpIDLField, usize),
    (_, _, _): (usize, Token, usize),
) -> TmpIDLField
{
    __0
}

fn __action80<
>(
    (_, __0, _): (usize, TypeField, usize),
) -> ::std::option::Option<TypeField>
{
    Some(__0)
}

fn __action81<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::option::Option<TypeField>
{
    None
}

fn __action82<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::vec::Vec<TypeField>
{
    vec![]
}

fn __action83<
>(
    (_, v, _): (usize, ::std::vec::Vec<TypeField>, usize),
) -> ::std::vec::Vec<TypeField>
{
    v
}

fn __action84<
>(
    (_, __0, _): (usize, TypeField, usize),
    (_, _, _): (usize, Token, usize),
) -> TypeField
{
    __0
}

fn __action85<
>(
    (_, __0, _): (usize, TypeField, usize),
) -> ::std::option::Option<TypeField>
{
    Some(__0)
}

fn __action86<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::option::Option<TypeField>
{
    None
}

fn __action87<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::vec::Vec<TypeField>
{
    vec![]
}

fn __action88<
>(
    (_, v, _): (usize, ::std::vec::Vec<TypeField>, usize),
) -> ::std::vec::Vec<TypeField>
{
    v
}

fn __action89<
>(
    (_, __0, _): (usize, TypeField, usize),
    (_, _, _): (usize, Token, usize),
) -> TypeField
{
    __0
}

fn __action90<
>(
    (_, __0, _): (usize, IDLType, usize),
) -> ::std::option::Option<IDLType>
{
    Some(__0)
}

fn __action91<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::option::Option<IDLType>
{
    None
}

fn __action92<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::vec::Vec<IDLType>
{
    vec![]
}

fn __action93<
>(
    (_, v, _): (usize, ::std::vec::Vec<IDLType>, usize),
) -> ::std::vec::Vec<IDLType>
{
    v
}

fn __action94<
>(
    (_, __0, _): (usize, IDLType, usize),
    (_, _, _): (usize, Token, usize),
) -> IDLType
{
    __0
}

fn __action95<
>(
    (_, __0, _): (usize, FuncMode, usize),
) -> ::std::vec::Vec<FuncMode>
{
    vec![__0]
}

fn __action96<
>(
    (_, v, _): (usize, ::std::vec::Vec<FuncMode>, usize),
    (_, e, _): (usize, FuncMode, usize),
) -> ::std::vec::Vec<FuncMode>
{
    { let mut v = v; v.push(e); v }
}

fn __action97<
>(
    (_, __0, _): (usize, Binding, usize),
) -> ::std::option::Option<Binding>
{
    Some(__0)
}

fn __action98<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::option::Option<Binding>
{
    None
}

fn __action99<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::vec::Vec<Binding>
{
    vec![]
}

fn __action100<
>(
    (_, v, _): (usize, ::std::vec::Vec<Binding>, usize),
) -> ::std::vec::Vec<Binding>
{
    v
}

fn __action101<
>(
    (_, __0, _): (usize, Binding, usize),
    (_, _, _): (usize, Token, usize),
) -> Binding
{
    __0
}

fn __action102<
>(
    (_, __0, _): (usize, Dec, usize),
) -> ::std::option::Option<Dec>
{
    Some(__0)
}

fn __action103<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::option::Option<Dec>
{
    None
}

fn __action104<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> ::std::vec::Vec<Dec>
{
    vec![]
}

fn __action105<
>(
    (_, v, _): (usize, ::std::vec::Vec<Dec>, usize),
) -> ::std::vec::Vec<Dec>
{
    v
}

fn __action106<
>(
    (_, __0, _): (usize, Dec, usize),
    (_, _, _): (usize, Token, usize),
) -> Dec
{
    __0
}

fn __action107<
>(
    (_, __0, _): (usize, Dec, usize),
) -> ::std::vec::Vec<Dec>
{
    vec![__0]
}

fn __action108<
>(
    (_, v, _): (usize, ::std::vec::Vec<Dec>, usize),
    (_, e, _): (usize, Dec, usize),
) -> ::std::vec::Vec<Dec>
{
    { let mut v = v; v.push(e); v }
}

fn __action109<
>(
    (_, __0, _): (usize, Binding, usize),
) -> ::std::vec::Vec<Binding>
{
    vec![__0]
}

fn __action110<
>(
    (_, v, _): (usize, ::std::vec::Vec<Binding>, usize),
    (_, e, _): (usize, Binding, usize),
) -> ::std::vec::Vec<Binding>
{
    { let mut v = v; v.push(e); v }
}

fn __action111<
>(
    (_, __0, _): (usize, IDLType, usize),
) -> ::std::vec::Vec<IDLType>
{
    vec![__0]
}

fn __action112<
>(
    (_, v, _): (usize, ::std::vec::Vec<IDLType>, usize),
    (_, e, _): (usize, IDLType, usize),
) -> ::std::vec::Vec<IDLType>
{
    { let mut v = v; v.push(e); v }
}

fn __action113<
>(
    (_, __0, _): (usize, TypeField, usize),
) -> ::std::vec::Vec<TypeField>
{
    vec![__0]
}

fn __action114<
>(
    (_, v, _): (usize, ::std::vec::Vec<TypeField>, usize),
    (_, e, _): (usize, TypeField, usize),
) -> ::std::vec::Vec<TypeField>
{
    { let mut v = v; v.push(e); v }
}

fn __action115<
>(
    (_, __0, _): (usize, TypeField, usize),
) -> ::std::vec::Vec<TypeField>
{
    vec![__0]
}

fn __action116<
>(
    (_, v, _): (usize, ::std::vec::Vec<TypeField>, usize),
    (_, e, _): (usize, TypeField, usize),
) -> ::std::vec::Vec<TypeField>
{
    { let mut v = v; v.push(e); v }
}

fn __action117<
>(
    (_, __0, _): (usize, TmpIDLField, usize),
) -> ::std::vec::Vec<TmpIDLField>
{
    vec![__0]
}

fn __action118<
>(
    (_, v, _): (usize, ::std::vec::Vec<TmpIDLField>, usize),
    (_, e, _): (usize, TmpIDLField, usize),
) -> ::std::vec::Vec<TmpIDLField>
{
    { let mut v = v; v.push(e); v }
}

fn __action119<
>(
    (_, __0, _): (usize, IDLValue, usize),
) -> ::std::vec::Vec<IDLValue>
{
    vec![__0]
}

fn __action120<
>(
    (_, v, _): (usize, ::std::vec::Vec<IDLValue>, usize),
    (_, e, _): (usize, IDLValue, usize),
) -> ::std::vec::Vec<IDLValue>
{
    { let mut v = v; v.push(e); v }
}

fn __action121<
>(
    (_, __0, _): (usize, IDLValue, usize),
) -> ::std::vec::Vec<IDLValue>
{
    vec![__0]
}

fn __action122<
>(
    (_, v, _): (usize, ::std::vec::Vec<IDLValue>, usize),
    (_, e, _): (usize, IDLValue, usize),
) -> ::std::vec::Vec<IDLValue>
{
    { let mut v = v; v.push(e); v }
}

fn __action123<
>(
    __0: (usize, Token, usize),
    __1: (usize, String, usize),
    __2: (usize, Token, usize),
    __3: (usize, Vec<Binding>, usize),
) -> IDLType
{
    let __start0 = __1.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action56(
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action48(
        __0,
        __temp0,
        __2,
        __3,
    )
}

fn __action124<
>(
    __0: (usize, Token, usize),
    __1: (usize, Token, usize),
    __2: (usize, Vec<Binding>, usize),
) -> IDLType
{
    let __start0 = __0.2.clone();
    let __end0 = __1.0.clone();
    let __temp0 = __action57(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action48(
        __0,
        __temp0,
        __1,
        __2,
    )
}

fn __action125<
>(
    __0: (usize, Token, usize),
    __1: (usize, String, usize),
    __2: (usize, Token, usize),
    __3: (usize, String, usize),
) -> IDLType
{
    let __start0 = __1.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action56(
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action49(
        __0,
        __temp0,
        __2,
        __3,
    )
}

fn __action126<
>(
    __0: (usize, Token, usize),
    __1: (usize, Token, usize),
    __2: (usize, String, usize),
) -> IDLType
{
    let __start0 = __0.2.clone();
    let __end0 = __1.0.clone();
    let __temp0 = __action57(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action49(
        __0,
        __temp0,
        __1,
        __2,
    )
}

fn __action127<
>(
    __0: (usize, IDLValue, usize),
    __1: (usize, Token, usize),
) -> ::std::vec::Vec<IDLValue>
{
    let __start0 = __0.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action69(
        __0,
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action121(
        __temp0,
    )
}

fn __action128<
>(
    __0: (usize, ::std::vec::Vec<IDLValue>, usize),
    __1: (usize, IDLValue, usize),
    __2: (usize, Token, usize),
) -> ::std::vec::Vec<IDLValue>
{
    let __start0 = __1.0.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action69(
        __1,
        __2,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action122(
        __0,
        __temp0,
    )
}

fn __action129<
>(
    __0: (usize, ::std::option::Option<IDLValue>, usize),
) -> Vec<IDLValue>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action67(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action66(
        __temp0,
        __0,
    )
}

fn __action130<
>(
    __0: (usize, ::std::vec::Vec<IDLValue>, usize),
    __1: (usize, ::std::option::Option<IDLValue>, usize),
) -> Vec<IDLValue>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action68(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action66(
        __temp0,
        __1,
    )
}

fn __action131<
>(
    __0: (usize, IDLValue, usize),
    __1: (usize, Token, usize),
) -> ::std::vec::Vec<IDLValue>
{
    let __start0 = __0.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action74(
        __0,
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action119(
        __temp0,
    )
}

fn __action132<
>(
    __0: (usize, ::std::vec::Vec<IDLValue>, usize),
    __1: (usize, IDLValue, usize),
    __2: (usize, Token, usize),
) -> ::std::vec::Vec<IDLValue>
{
    let __start0 = __1.0.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action74(
        __1,
        __2,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action120(
        __0,
        __temp0,
    )
}

fn __action133<
>(
    __0: (usize, ::std::option::Option<IDLValue>, usize),
) -> Vec<IDLValue>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action72(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action65(
        __temp0,
        __0,
    )
}

fn __action134<
>(
    __0: (usize, ::std::vec::Vec<IDLValue>, usize),
    __1: (usize, ::std::option::Option<IDLValue>, usize),
) -> Vec<IDLValue>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action73(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action65(
        __temp0,
        __1,
    )
}

fn __action135<
>(
    __0: (usize, IDLType, usize),
    __1: (usize, Token, usize),
) -> ::std::vec::Vec<IDLType>
{
    let __start0 = __0.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action94(
        __0,
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action111(
        __temp0,
    )
}

fn __action136<
>(
    __0: (usize, ::std::vec::Vec<IDLType>, usize),
    __1: (usize, IDLType, usize),
    __2: (usize, Token, usize),
) -> ::std::vec::Vec<IDLType>
{
    let __start0 = __1.0.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action94(
        __1,
        __2,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action112(
        __0,
        __temp0,
    )
}

fn __action137<
>(
    __0: (usize, ::std::option::Option<IDLType>, usize),
) -> Vec<IDLType>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action92(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action61(
        __temp0,
        __0,
    )
}

fn __action138<
>(
    __0: (usize, ::std::vec::Vec<IDLType>, usize),
    __1: (usize, ::std::option::Option<IDLType>, usize),
) -> Vec<IDLType>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action93(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action61(
        __temp0,
        __1,
    )
}

fn __action139<
>(
    __0: (usize, Dec, usize),
    __1: (usize, Token, usize),
) -> ::std::vec::Vec<Dec>
{
    let __start0 = __0.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action106(
        __0,
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action107(
        __temp0,
    )
}

fn __action140<
>(
    __0: (usize, ::std::vec::Vec<Dec>, usize),
    __1: (usize, Dec, usize),
    __2: (usize, Token, usize),
) -> ::std::vec::Vec<Dec>
{
    let __start0 = __1.0.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action106(
        __1,
        __2,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action108(
        __0,
        __temp0,
    )
}

fn __action141<
>(
    __0: (usize, ::std::option::Option<Dec>, usize),
) -> Vec<Dec>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action104(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action55(
        __temp0,
        __0,
    )
}

fn __action142<
>(
    __0: (usize, ::std::vec::Vec<Dec>, usize),
    __1: (usize, ::std::option::Option<Dec>, usize),
) -> Vec<Dec>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action105(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action55(
        __temp0,
        __1,
    )
}

fn __action143<
>(
    __0: (usize, Binding, usize),
    __1: (usize, Token, usize),
) -> ::std::vec::Vec<Binding>
{
    let __start0 = __0.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action101(
        __0,
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action109(
        __temp0,
    )
}

fn __action144<
>(
    __0: (usize, ::std::vec::Vec<Binding>, usize),
    __1: (usize, Binding, usize),
    __2: (usize, Token, usize),
) -> ::std::vec::Vec<Binding>
{
    let __start0 = __1.0.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action101(
        __1,
        __2,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action110(
        __0,
        __temp0,
    )
}

fn __action145<
>(
    __0: (usize, ::std::option::Option<Binding>, usize),
) -> Vec<Binding>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action99(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action58(
        __temp0,
        __0,
    )
}

fn __action146<
>(
    __0: (usize, ::std::vec::Vec<Binding>, usize),
    __1: (usize, ::std::option::Option<Binding>, usize),
) -> Vec<Binding>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action100(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action58(
        __temp0,
        __1,
    )
}

fn __action147<
>(
    __0: (usize, TmpIDLField, usize),
    __1: (usize, Token, usize),
) -> ::std::vec::Vec<TmpIDLField>
{
    let __start0 = __0.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action79(
        __0,
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action117(
        __temp0,
    )
}

fn __action148<
>(
    __0: (usize, ::std::vec::Vec<TmpIDLField>, usize),
    __1: (usize, TmpIDLField, usize),
    __2: (usize, Token, usize),
) -> ::std::vec::Vec<TmpIDLField>
{
    let __start0 = __1.0.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action79(
        __1,
        __2,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action118(
        __0,
        __temp0,
    )
}

fn __action149<
>(
    __0: (usize, ::std::option::Option<TmpIDLField>, usize),
) -> Vec<TmpIDLField>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action77(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action64(
        __temp0,
        __0,
    )
}

fn __action150<
>(
    __0: (usize, ::std::vec::Vec<TmpIDLField>, usize),
    __1: (usize, ::std::option::Option<TmpIDLField>, usize),
) -> Vec<TmpIDLField>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action78(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action64(
        __temp0,
        __1,
    )
}

fn __action151<
>(
    __0: (usize, TypeField, usize),
    __1: (usize, Token, usize),
) -> ::std::vec::Vec<TypeField>
{
    let __start0 = __0.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action84(
        __0,
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action115(
        __temp0,
    )
}

fn __action152<
>(
    __0: (usize, ::std::vec::Vec<TypeField>, usize),
    __1: (usize, TypeField, usize),
    __2: (usize, Token, usize),
) -> ::std::vec::Vec<TypeField>
{
    let __start0 = __1.0.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action84(
        __1,
        __2,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action116(
        __0,
        __temp0,
    )
}

fn __action153<
>(
    __0: (usize, ::std::option::Option<TypeField>, usize),
) -> Vec<TypeField>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action82(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action63(
        __temp0,
        __0,
    )
}

fn __action154<
>(
    __0: (usize, ::std::vec::Vec<TypeField>, usize),
    __1: (usize, ::std::option::Option<TypeField>, usize),
) -> Vec<TypeField>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action83(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action63(
        __temp0,
        __1,
    )
}

fn __action155<
>(
    __0: (usize, TypeField, usize),
    __1: (usize, Token, usize),
) -> ::std::vec::Vec<TypeField>
{
    let __start0 = __0.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action89(
        __0,
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action113(
        __temp0,
    )
}

fn __action156<
>(
    __0: (usize, ::std::vec::Vec<TypeField>, usize),
    __1: (usize, TypeField, usize),
    __2: (usize, Token, usize),
) -> ::std::vec::Vec<TypeField>
{
    let __start0 = __1.0.clone();
    let __end0 = __2.2.clone();
    let __temp0 = __action89(
        __1,
        __2,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action114(
        __0,
        __temp0,
    )
}

fn __action157<
>(
    __0: (usize, ::std::option::Option<TypeField>, usize),
) -> Vec<TypeField>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.0.clone();
    let __temp0 = __action87(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action62(
        __temp0,
        __0,
    )
}

fn __action158<
>(
    __0: (usize, ::std::vec::Vec<TypeField>, usize),
    __1: (usize, ::std::option::Option<TypeField>, usize),
) -> Vec<TypeField>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action88(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action62(
        __temp0,
        __1,
    )
}

fn __action159<
>(
    __0: (usize, Vec<Dec>, usize),
    __1: (usize, IDLType, usize),
) -> IDLProg
{
    let __start0 = __1.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action53(
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action50(
        __0,
        __temp0,
    )
}

fn __action160<
>(
    __0: (usize, Vec<Dec>, usize),
) -> IDLProg
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action54(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action50(
        __0,
        __temp0,
    )
}

fn __action161<
>(
    __0: (usize, IDLValue, usize),
) -> Vec<IDLValue>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action70(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action129(
        __temp0,
    )
}

fn __action162<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> Vec<IDLValue>
{
    let __start0 = __lookbehind.clone();
    let __end0 = __lookahead.clone();
    let __temp0 = __action71(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action129(
        __temp0,
    )
}

fn __action163<
>(
    __0: (usize, ::std::vec::Vec<IDLValue>, usize),
    __1: (usize, IDLValue, usize),
) -> Vec<IDLValue>
{
    let __start0 = __1.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action70(
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action130(
        __0,
        __temp0,
    )
}

fn __action164<
>(
    __0: (usize, ::std::vec::Vec<IDLValue>, usize),
) -> Vec<IDLValue>
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action71(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action130(
        __0,
        __temp0,
    )
}

fn __action165<
>(
    __0: (usize, IDLValue, usize),
) -> Vec<IDLValue>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action70(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action133(
        __temp0,
    )
}

fn __action166<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> Vec<IDLValue>
{
    let __start0 = __lookbehind.clone();
    let __end0 = __lookahead.clone();
    let __temp0 = __action71(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action133(
        __temp0,
    )
}

fn __action167<
>(
    __0: (usize, ::std::vec::Vec<IDLValue>, usize),
    __1: (usize, IDLValue, usize),
) -> Vec<IDLValue>
{
    let __start0 = __1.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action70(
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action134(
        __0,
        __temp0,
    )
}

fn __action168<
>(
    __0: (usize, ::std::vec::Vec<IDLValue>, usize),
) -> Vec<IDLValue>
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action71(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action134(
        __0,
        __temp0,
    )
}

fn __action169<
>(
    __0: (usize, IDLType, usize),
) -> Vec<IDLType>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action90(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action137(
        __temp0,
    )
}

fn __action170<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> Vec<IDLType>
{
    let __start0 = __lookbehind.clone();
    let __end0 = __lookahead.clone();
    let __temp0 = __action91(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action137(
        __temp0,
    )
}

fn __action171<
>(
    __0: (usize, ::std::vec::Vec<IDLType>, usize),
    __1: (usize, IDLType, usize),
) -> Vec<IDLType>
{
    let __start0 = __1.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action90(
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action138(
        __0,
        __temp0,
    )
}

fn __action172<
>(
    __0: (usize, ::std::vec::Vec<IDLType>, usize),
) -> Vec<IDLType>
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action91(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action138(
        __0,
        __temp0,
    )
}

fn __action173<
>(
    __0: (usize, Dec, usize),
) -> Vec<Dec>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action102(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action141(
        __temp0,
    )
}

fn __action174<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> Vec<Dec>
{
    let __start0 = __lookbehind.clone();
    let __end0 = __lookahead.clone();
    let __temp0 = __action103(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action141(
        __temp0,
    )
}

fn __action175<
>(
    __0: (usize, ::std::vec::Vec<Dec>, usize),
    __1: (usize, Dec, usize),
) -> Vec<Dec>
{
    let __start0 = __1.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action102(
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action142(
        __0,
        __temp0,
    )
}

fn __action176<
>(
    __0: (usize, ::std::vec::Vec<Dec>, usize),
) -> Vec<Dec>
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action103(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action142(
        __0,
        __temp0,
    )
}

fn __action177<
>(
    __0: (usize, Token, usize),
    __1: (usize, Vec<IDLType>, usize),
    __2: (usize, Token, usize),
    __3: (usize, Token, usize),
    __4: (usize, Token, usize),
    __5: (usize, Vec<IDLType>, usize),
    __6: (usize, Token, usize),
) -> FuncType
{
    let __start0 = __6.2.clone();
    let __end0 = __6.2.clone();
    let __temp0 = __action59(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action38(
        __0,
        __1,
        __2,
        __3,
        __4,
        __5,
        __6,
        __temp0,
    )
}

fn __action178<
>(
    __0: (usize, Token, usize),
    __1: (usize, Vec<IDLType>, usize),
    __2: (usize, Token, usize),
    __3: (usize, Token, usize),
    __4: (usize, Token, usize),
    __5: (usize, Vec<IDLType>, usize),
    __6: (usize, Token, usize),
    __7: (usize, ::std::vec::Vec<FuncMode>, usize),
) -> FuncType
{
    let __start0 = __7.0.clone();
    let __end0 = __7.2.clone();
    let __temp0 = __action60(
        __7,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action38(
        __0,
        __1,
        __2,
        __3,
        __4,
        __5,
        __6,
        __temp0,
    )
}

fn __action179<
>(
    __0: (usize, Binding, usize),
) -> Vec<Binding>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action97(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action145(
        __temp0,
    )
}

fn __action180<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> Vec<Binding>
{
    let __start0 = __lookbehind.clone();
    let __end0 = __lookahead.clone();
    let __temp0 = __action98(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action145(
        __temp0,
    )
}

fn __action181<
>(
    __0: (usize, ::std::vec::Vec<Binding>, usize),
    __1: (usize, Binding, usize),
) -> Vec<Binding>
{
    let __start0 = __1.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action97(
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action146(
        __0,
        __temp0,
    )
}

fn __action182<
>(
    __0: (usize, ::std::vec::Vec<Binding>, usize),
) -> Vec<Binding>
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action98(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action146(
        __0,
        __temp0,
    )
}

fn __action183<
>(
    __0: (usize, TmpIDLField, usize),
) -> Vec<TmpIDLField>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action75(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action149(
        __temp0,
    )
}

fn __action184<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> Vec<TmpIDLField>
{
    let __start0 = __lookbehind.clone();
    let __end0 = __lookahead.clone();
    let __temp0 = __action76(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action149(
        __temp0,
    )
}

fn __action185<
>(
    __0: (usize, ::std::vec::Vec<TmpIDLField>, usize),
    __1: (usize, TmpIDLField, usize),
) -> Vec<TmpIDLField>
{
    let __start0 = __1.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action75(
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action150(
        __0,
        __temp0,
    )
}

fn __action186<
>(
    __0: (usize, ::std::vec::Vec<TmpIDLField>, usize),
) -> Vec<TmpIDLField>
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action76(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action150(
        __0,
        __temp0,
    )
}

fn __action187<
>(
    __0: (usize, TypeField, usize),
) -> Vec<TypeField>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action80(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action153(
        __temp0,
    )
}

fn __action188<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> Vec<TypeField>
{
    let __start0 = __lookbehind.clone();
    let __end0 = __lookahead.clone();
    let __temp0 = __action81(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action153(
        __temp0,
    )
}

fn __action189<
>(
    __0: (usize, ::std::vec::Vec<TypeField>, usize),
    __1: (usize, TypeField, usize),
) -> Vec<TypeField>
{
    let __start0 = __1.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action80(
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action154(
        __0,
        __temp0,
    )
}

fn __action190<
>(
    __0: (usize, ::std::vec::Vec<TypeField>, usize),
) -> Vec<TypeField>
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action81(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action154(
        __0,
        __temp0,
    )
}

fn __action191<
>(
    __0: (usize, TypeField, usize),
) -> Vec<TypeField>
{
    let __start0 = __0.0.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action85(
        __0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action157(
        __temp0,
    )
}

fn __action192<
>(
    __lookbehind: &usize,
    __lookahead: &usize,
) -> Vec<TypeField>
{
    let __start0 = __lookbehind.clone();
    let __end0 = __lookahead.clone();
    let __temp0 = __action86(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action157(
        __temp0,
    )
}

fn __action193<
>(
    __0: (usize, ::std::vec::Vec<TypeField>, usize),
    __1: (usize, TypeField, usize),
) -> Vec<TypeField>
{
    let __start0 = __1.0.clone();
    let __end0 = __1.2.clone();
    let __temp0 = __action85(
        __1,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action158(
        __0,
        __temp0,
    )
}

fn __action194<
>(
    __0: (usize, ::std::vec::Vec<TypeField>, usize),
) -> Vec<TypeField>
{
    let __start0 = __0.2.clone();
    let __end0 = __0.2.clone();
    let __temp0 = __action86(
        &__start0,
        &__end0,
    );
    let __temp0 = (__start0, __temp0, __end0);
    __action158(
        __0,
        __temp0,
    )
}

pub trait __ToTriple<> {
    fn to_triple(value: Self) -> Result<(usize,Token,usize), __lalrpop_util::ParseError<usize, Token, LexicalError>>;
}

impl<> __ToTriple<> for (usize, Token, usize) {
    fn to_triple(value: Self) -> Result<(usize,Token,usize), __lalrpop_util::ParseError<usize, Token, LexicalError>> {
        Ok(value)
    }
}
impl<> __ToTriple<> for Result<(usize, Token, usize), LexicalError> {
    fn to_triple(value: Self) -> Result<(usize,Token,usize), __lalrpop_util::ParseError<usize, Token, LexicalError>> {
        match value {
            Ok(v) => Ok(v),
            Err(error) => Err(__lalrpop_util::ParseError::User { error }),
        }
    }
}
