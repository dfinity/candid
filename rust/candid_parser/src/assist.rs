use anyhow::Result;
use candid::types::{
    internal::text_size,
    value::{IDLField, IDLValue, VariantValue},
    Type, TypeEnv, TypeInner,
};
use candid::{IDLArgs, Int, Nat, Principal};
use dialoguer::{theme::ColorfulTheme, Confirm, Editor, Input, Select};
use std::path::Path;

fn show_type(ty: &Type) -> String {
    if text_size(ty, 80).is_ok() {
        format!(" : {ty}")
    } else {
        String::new()
    }
}
fn parse_blob(s: &str) -> Result<Vec<u8>> {
    let raw = format!("blob \"{}\"", s);
    if let IDLValue::Blob(blob) = crate::parse_idl_value(&raw)? {
        Ok(blob)
    } else {
        Err(anyhow::anyhow!("Invalid blob"))
    }
}

/// Ask for user input from terminal based on the provided Candid types. A textual version of Candid UI.
pub fn input_args(env: &TypeEnv, tys: &[Type]) -> Result<IDLArgs> {
    let len = tys.len();
    let mut args = Vec::new();
    for (i, ty) in tys.iter().enumerate() {
        if len > 1 {
            println!("Enter argument {} of {}:", i + 1, len);
        }
        let val = input(env, ty)?;
        args.push(val);
    }
    Ok(IDLArgs { args })
}

/// Ask for user input from terminal based on the provided Candid type. A textual version of Candid UI.
pub fn input(env: &TypeEnv, ty: &Type) -> Result<IDLValue> {
    let theme = ColorfulTheme::default();
    let style = console::Style::new().bright().green();
    Ok(match ty.as_ref() {
        TypeInner::Reserved => IDLValue::Reserved,
        TypeInner::Null => IDLValue::Null,
        TypeInner::Knot(_) | TypeInner::Unknown | TypeInner::Future | TypeInner::Class(_, _) => {
            unreachable!()
        }
        TypeInner::Empty => unreachable!(), // TODO: proactively avoid empty
        TypeInner::Var(id) => {
            let t = env.rec_find_type(id)?;
            println!("Enter a value for {}{}", style.apply_to(id), show_type(t));
            input(env, t)?
        }
        TypeInner::Bool => {
            let v = Select::with_theme(&theme)
                .with_prompt("Select a bool")
                .items(&["false", "true"])
                .interact()?;
            IDLValue::Bool(v == 1)
        }
        TypeInner::Int => IDLValue::Int(
            Input::<Int>::with_theme(&theme)
                .with_prompt("Enter an int")
                .interact_text()?,
        ),
        TypeInner::Nat => IDLValue::Nat(
            Input::<Nat>::with_theme(&theme)
                .with_prompt("Enter a nat")
                .interact_text()?,
        ),
        TypeInner::Nat8 => IDLValue::Nat8(
            Input::<u8>::with_theme(&theme)
                .with_prompt("Enter a nat8")
                .interact_text()?,
        ),
        TypeInner::Nat16 => IDLValue::Nat16(
            Input::<u16>::with_theme(&theme)
                .with_prompt("Enter a nat16")
                .interact_text()?,
        ),
        TypeInner::Nat32 => IDLValue::Nat32(
            Input::<u32>::with_theme(&theme)
                .with_prompt("Enter a nat32")
                .interact_text()?,
        ),
        TypeInner::Nat64 => IDLValue::Nat64(
            Input::<u64>::with_theme(&theme)
                .with_prompt("Enter a nat64")
                .interact_text()?,
        ),
        TypeInner::Int8 => IDLValue::Int8(
            Input::<i8>::with_theme(&theme)
                .with_prompt("Enter an int8")
                .interact_text()?,
        ),
        TypeInner::Int16 => IDLValue::Int16(
            Input::<i16>::with_theme(&theme)
                .with_prompt("Enter an int16")
                .interact_text()?,
        ),
        TypeInner::Int32 => IDLValue::Int32(
            Input::<i32>::with_theme(&theme)
                .with_prompt("Enter an int32")
                .interact_text()?,
        ),
        TypeInner::Int64 => IDLValue::Int64(
            Input::<i64>::with_theme(&theme)
                .with_prompt("Enter an int64")
                .interact_text()?,
        ),
        TypeInner::Float32 => IDLValue::Float32(
            Input::<f32>::with_theme(&theme)
                .with_prompt("Enter a float32")
                .interact_text()?,
        ),
        TypeInner::Float64 => IDLValue::Float64(
            Input::<f64>::with_theme(&theme)
                .with_prompt("Enter a float64")
                .interact_text()?,
        ),
        TypeInner::Text => {
            let text = Input::<String>::with_theme(&theme)
                .allow_empty(true)
                .with_prompt("Enter a text (type :e to use editor)")
                .interact()?;
            let text = if text == ":e" {
                if let Some(rv) = Editor::new().edit("Enter your text")? {
                    rv
                } else {
                    String::new()
                }
            } else {
                text
            };
            IDLValue::Text(text)
        }
        TypeInner::Opt(ty) => {
            let yes = Confirm::with_theme(&theme)
                .with_prompt("Do you want to enter an optional value?")
                .interact()?;
            if yes {
                let val = input(env, ty)?;
                IDLValue::Opt(Box::new(val))
            } else {
                IDLValue::None
            }
        }
        TypeInner::Vec(_) if ty.is_blob(env) => {
            let mode = Select::with_theme(&theme)
                .with_prompt("Select a way to enter blob")
                .default(0)
                .items(&["blob", "hex", "file"])
                .interact()?;
            let blob = match mode {
                0 => {
                    let raw = Input::<String>::with_theme(&theme)
                        .with_prompt("Enter a blob (characters or \\xx)")
                        .validate_with(|s: &String| parse_blob(s).map(|_| ()))
                        .allow_empty(true)
                        .interact()?;
                    parse_blob(&raw)?
                }
                1 => {
                    let blob = Input::<String>::with_theme(&theme)
                        .with_prompt("Enter hex string")
                        .allow_empty(true)
                        .validate_with(|s: &String| {
                            if s.len() % 2 == 0 && s.chars().all(|c| c.is_ascii_hexdigit()) {
                                Ok(())
                            } else {
                                Err("Invalid hex string")
                            }
                        })
                        .interact_text()?;
                    hex::decode(blob)?
                }
                2 => {
                    let path = Input::<String>::with_theme(&theme)
                        .with_prompt("Enter a file path")
                        .validate_with(|s: &String| {
                            if Path::new(s).exists() {
                                Ok(())
                            } else {
                                Err("File doesn't exist")
                            }
                        })
                        .interact()?;
                    std::fs::read(path)?
                }

                _ => unreachable!(),
            };
            IDLValue::Blob(blob)
        }
        TypeInner::Vec(ty) => {
            let mut vals = Vec::new();
            loop {
                let yes = Confirm::with_theme(&theme)
                    .with_prompt("Do you want to enter a new vector element?")
                    .interact()?;
                if yes {
                    let val = input(env, ty)?;
                    vals.push(val);
                } else {
                    break;
                }
            }
            IDLValue::Vec(vals)
        }
        TypeInner::Record(fs) => {
            let mut fields = Vec::new();
            for f in fs.iter() {
                let name = style.apply_to(format!("{}", f.id));
                let val = if let TypeInner::Opt(ty) = env.trace_type(&f.ty)?.as_ref() {
                    let prompt = format!("Enter optional field {name}{}?", show_type(&f.ty));
                    let yes = Confirm::with_theme(&theme).with_prompt(prompt).interact()?;
                    if yes {
                        IDLValue::Opt(Box::new(input(env, ty)?))
                    } else {
                        IDLValue::None
                    }
                } else {
                    println!("Enter field {name}{}", show_type(&f.ty));
                    input(env, &f.ty)?
                };
                fields.push(IDLField {
                    id: (*f.id).clone(),
                    val,
                });
            }
            IDLValue::Record(fields)
        }
        TypeInner::Variant(fs) => {
            let tags: Vec<_> = fs.iter().map(|f| format!("{}", f.id)).collect();
            let idx = Select::with_theme(&theme)
                .with_prompt("Select a variant")
                .items(&tags)
                .interact()?;
            let val = input(env, &fs[idx].ty)?;
            let field = IDLField {
                id: (*fs[idx].id).clone(),
                val,
            };
            IDLValue::Variant(VariantValue(Box::new(field), idx as u64))
        }
        TypeInner::Principal => IDLValue::Principal(
            Input::<Principal>::with_theme(&theme)
                .with_prompt("Enter a principal")
                .interact()?,
        ),
        TypeInner::Service(_) => IDLValue::Service(
            Input::<Principal>::with_theme(&theme)
                .with_prompt("Enter a canister id")
                .interact()?,
        ),
        TypeInner::Func(_) => {
            let id = Input::<Principal>::with_theme(&theme)
                .with_prompt("Enter a canister id")
                .interact()?;
            let method = Input::<String>::with_theme(&theme)
                .with_prompt("Enter a method name")
                .interact()?;
            IDLValue::Func(id, method)
        }
    })
}
