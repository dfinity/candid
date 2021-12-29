use crate::error::Result;
use crate::Error::Custom;
use crate::{pretty_check_file, types};
use anyhow::Error;
use std::collections::HashSet;
use std::path::PathBuf;

// can be extended to other sources such as strings and streams
pub enum Source {
    File(PathBuf),
}

// checks the input is valid and input is subtype of previous if previous is Some
pub fn check(input: Source, previous: Option<Source>) -> Result<()> {
    with_source(input, |input| {
        let (mut env, opt_t1) = pretty_check_file(input)?;
        if let Some(previous) = previous {
            with_source(previous, |previous| {
                let (env2, opt_t2) = pretty_check_file(previous)?;
                match (opt_t1, opt_t2) {
                    (Some(t1), Some(t2)) => {
                        let mut gamma = HashSet::new();
                        let t2 = env.merge_type(env2, t2);
                        types::subtype::subtype(&mut gamma, &env, &t1, &t2)
                    }
                    (None, _) => {
                        let msg = format!(
                            "did file {} must contain the main service type for subtyping check",
                            input.display()
                        );
                        Err(Custom(Error::msg(msg)))
                    }
                    _ => {
                        let msg = format!(
                            "did file {} must contain the main service type for subtyping check",
                            previous.display()
                        );
                        Err(Custom(Error::msg(msg)))
                    }
                }
            })
        } else {
            Ok(())
        }
    })
}

fn with_source(source: Source, f: impl FnOnce(&PathBuf) -> Result<()>) -> Result<()> {
    match source {
        Source::File(file) => f(&file),
    }
}
