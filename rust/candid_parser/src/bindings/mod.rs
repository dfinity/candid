//! Candid bindings for different languages.
// This module assumes the input are type checked, it is safe to use unwrap.

// pub mod candid;
pub use ::candid::bindings::candid;

#[cfg_attr(docsrs, doc(cfg(feature = "parser")))]
#[cfg(feature = "parser")]
pub mod analysis;
#[cfg_attr(docsrs, doc(cfg(feature = "parser")))]
#[cfg(feature = "parser")]
pub mod javascript;
#[cfg_attr(docsrs, doc(cfg(feature = "parser")))]
#[cfg(feature = "parser")]
pub mod motoko;
#[cfg_attr(docsrs, doc(cfg(feature = "parser")))]
#[cfg(feature = "parser")]
pub mod rust;
#[cfg_attr(docsrs, doc(cfg(feature = "parser")))]
#[cfg(feature = "parser")]
pub mod typescript;
