use crate::parse_idl_value;
use anyhow::Result;
use candid::types::{
    internal::text_size,
    value::{IDLField, IDLValue, VariantValue},
    Type, TypeEnv, TypeInner,
};
use candid::{IDLArgs, Int, Nat, Principal};
use console::{style, Style, StyledObject};
use dialoguer::{theme::Theme, Completion, Confirm, Editor, Input, Select};
use std::collections::BTreeMap;
use std::fmt;
use std::path::Path;

pub struct Context {
    env: TypeEnv,
    completion: BTreeMap<String, BTreeMap<String, String>>,
}
impl Context {
    pub fn new(env: TypeEnv) -> Self {
        let mut completion = BTreeMap::new();
        let principal: BTreeMap<String, String> = [("ic", "aaaaa-aa"), ("anonymous", "2vxsx-fae")]
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect();
        completion.insert("principal".to_string(), principal);
        Self { env, completion }
    }
    pub fn set_completion(
        &mut self,
        list: BTreeMap<String, BTreeMap<String, String>>,
    ) -> &mut Self {
        self.completion = list;
        self
    }
    fn project_type(&self, typ: &str) -> Candidate {
        let inner = match self.completion.get(typ) {
            None => BTreeMap::new(),
            Some(m) => m.clone(),
        };
        Candidate { inner }
    }
}

/// Ask for user input from terminal based on the provided Candid types. A textual version of Candid UI.
pub fn input_args(ctx: &Context, tys: &[Type]) -> Result<IDLArgs> {
    // Patch ctrlc untill https://github.com/console-rs/dialoguer/issues/77 is fixed
    let _ = ctrlc::try_set_handler(move || {
        let term = console::Term::stdout();
        let _ = term.show_cursor();
    });
    let len = tys.len();
    let mut args = Vec::new();
    for (i, ty) in tys.iter().enumerate() {
        if len > 1 {
            println!("Enter argument {} of {}:", i + 1, len);
        }
        let val = input(ctx, ty, 0)?;
        args.push(val);
    }
    Ok(IDLArgs { args })
}

/// Ask for user input from terminal based on the provided Candid type. A textual version of Candid UI.
pub fn input(ctx: &Context, ty: &Type, dep: usize) -> Result<IDLValue> {
    let theme = IndentTheme::new(dep);
    let style = theme.values_style.clone();
    Ok(match ty.as_ref() {
        TypeInner::Reserved => IDLValue::Reserved,
        TypeInner::Null => IDLValue::Null,
        TypeInner::Knot(_) | TypeInner::Unknown | TypeInner::Future | TypeInner::Class(_, _) => {
            unreachable!()
        }
        TypeInner::Empty => unreachable!(), // TODO: proactively avoid empty
        TypeInner::Var(id) => {
            let t = ctx.env.rec_find_type(id)?;
            theme.println(format!(
                "Enter a value for {}{}",
                style.apply_to(id),
                show_type(t)
            ));
            input(ctx, t, dep)?
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
                Editor::new().edit("Enter your text")?.unwrap_or_default()
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
                let val = input(ctx, ty, dep + 1)?;
                IDLValue::Opt(Box::new(val))
            } else {
                IDLValue::None
            }
        }
        TypeInner::Vec(_) if ty.is_blob(&ctx.env) => {
            let mode = Select::with_theme(&theme)
                .with_prompt("Select a way to enter blob")
                .default(0)
                .items(&["byte string", "hex", "file"])
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
                    let val = input(ctx, ty, dep + 1)?;
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
                let val = if let TypeInner::Opt(ty) = ctx.env.trace_type(&f.ty)?.as_ref() {
                    let prompt = format!("Enter optional field {name}{}?", show_type(&f.ty));
                    let yes = Confirm::with_theme(&theme).with_prompt(prompt).interact()?;
                    if yes {
                        IDLValue::Opt(Box::new(input(ctx, ty, dep + 1)?))
                    } else {
                        IDLValue::None
                    }
                } else {
                    theme.println(format!("Enter field {name}{}", show_type(&f.ty)));
                    input(ctx, &f.ty, dep + 1)?
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
            let val = input(ctx, &fs[idx].ty, dep + 1)?;
            let field = IDLField {
                id: (*fs[idx].id).clone(),
                val,
            };
            IDLValue::Variant(VariantValue(Box::new(field), idx as u64))
        }
        TypeInner::Principal => {
            let completion = get_candidate(ctx, &theme, "principal");
            IDLValue::Principal(
                Input::<Principal>::with_theme(&theme)
                    .with_prompt("Enter a principal")
                    .completion_with(&completion)
                    .interact_text()?,
            )
        }
        TypeInner::Service(_) => {
            let completion = get_candidate(ctx, &theme, "principal");
            IDLValue::Service(
                Input::<Principal>::with_theme(&theme)
                    .with_prompt("Enter a canister id")
                    .completion_with(&completion)
                    .interact_text()?,
            )
        }
        TypeInner::Func(_) => {
            let completion = get_candidate(ctx, &theme, "principal");
            let id = Input::<Principal>::with_theme(&theme)
                .with_prompt("Enter a canister id")
                .completion_with(&completion)
                .interact_text()?;
            let method = Input::<String>::with_theme(&theme)
                .with_prompt("Enter a method name")
                .interact()?;
            IDLValue::Func(id, method)
        }
    })
}

struct Candidate {
    inner: BTreeMap<String, String>,
}
impl Candidate {
    fn get_keys(&self) -> String {
        self.inner.keys().cloned().collect::<Vec<_>>().join(", ")
    }
}
impl Completion for Candidate {
    fn get(&self, input: &str) -> Option<String> {
        let matches: Vec<_> = self
            .inner
            .iter()
            .filter(|(k, _)| k.starts_with(input))
            .collect();
        if matches.len() == 1 {
            Some(matches[0].1.clone())
        } else {
            None
        }
    }
}
fn get_candidate(ctx: &Context, theme: &IndentTheme, ty: &str) -> Candidate {
    let completion = ctx.project_type(ty);
    let keys = completion.get_keys();
    if !keys.is_empty() {
        theme.hint(format!("Auto-completions: {keys}"));
    }
    completion
}

fn show_type(ty: &Type) -> String {
    if text_size(ty, 80).is_ok() {
        format!(" : {ty}")
    } else {
        String::new()
    }
}
fn parse_blob(s: &str) -> Result<Vec<u8>> {
    let raw = format!("blob \"{}\"", s);
    if let IDLValue::Blob(blob) = parse_idl_value(&raw)? {
        Ok(blob)
    } else {
        Err(anyhow::anyhow!("Invalid blob"))
    }
}

struct IndentTheme {
    indent: usize,
    defaults_style: Style,
    prompt_style: Style,
    prompt_prefix: StyledObject<String>,
    prompt_suffix: StyledObject<String>,
    success_prefix: StyledObject<String>,
    success_suffix: StyledObject<String>,
    error_prefix: StyledObject<String>,
    error_style: Style,
    hint_style: Style,
    values_style: Style,
    active_item_style: Style,
    inactive_item_style: Style,
    active_item_prefix: StyledObject<String>,
    inactive_item_prefix: StyledObject<String>,
}
impl IndentTheme {
    fn new(indent: usize) -> Self {
        Self {
            indent,
            defaults_style: Style::new().for_stderr().cyan(),
            prompt_style: Style::new().for_stderr().bold(),
            prompt_prefix: style("?".to_string()).for_stderr().yellow(),
            prompt_suffix: style("›".to_string()).for_stderr().black().bright(),
            success_prefix: style("✔".to_string()).for_stderr().green(),
            success_suffix: style("·".to_string()).for_stderr().black().bright(),
            error_prefix: style("✘".to_string()).for_stderr().red(),
            error_style: Style::new().for_stderr().red(),
            hint_style: Style::new().for_stderr().black().bright(),
            values_style: Style::new().for_stderr().green(),
            active_item_style: Style::new().for_stderr().cyan(),
            inactive_item_style: Style::new().for_stderr(),
            active_item_prefix: style("❯".to_string()).for_stderr().green(),
            inactive_item_prefix: style(" ".to_string()).for_stderr(),
        }
    }
    fn indent(&self, f: &mut dyn fmt::Write) -> fmt::Result {
        let spaces = " ".repeat(self.indent * 2);
        write!(f, "{spaces}")
    }
    fn println(&self, prompt: String) {
        let spaces = " ".repeat(self.indent * 2);
        println!("{spaces}{prompt}");
    }
    fn hint(&self, prompt: String) {
        let spaces = " ".repeat(self.indent * 2);
        println!("{spaces}{}", self.hint_style.apply_to(prompt));
    }
}
impl Theme for IndentTheme {
    fn format_prompt(&self, f: &mut dyn fmt::Write, prompt: &str) -> fmt::Result {
        self.indent(f)?;
        write!(
            f,
            "{} {} ",
            &self.prompt_prefix,
            self.prompt_style.apply_to(prompt)
        )?;
        write!(f, "{}", &self.prompt_suffix)
    }
    fn format_error(&self, f: &mut dyn fmt::Write, err: &str) -> fmt::Result {
        self.indent(f)?;
        write!(
            f,
            "{} {}",
            &self.error_prefix,
            self.error_style.apply_to(err)
        )
    }
    fn format_input_prompt(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        default: Option<&str>,
    ) -> fmt::Result {
        self.indent(f)?;
        if !prompt.is_empty() {
            write!(
                f,
                "{} {} ",
                &self.prompt_prefix,
                self.prompt_style.apply_to(prompt)
            )?;
        }

        match default {
            Some(default) => write!(
                f,
                "{} {} ",
                self.hint_style.apply_to(&format!("({})", default)),
                &self.prompt_suffix
            ),
            None => write!(f, "{} ", &self.prompt_suffix),
        }
    }
    fn format_confirm_prompt(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        default: Option<bool>,
    ) -> fmt::Result {
        self.indent(f)?;
        if !prompt.is_empty() {
            write!(
                f,
                "{} {} ",
                &self.prompt_prefix,
                self.prompt_style.apply_to(prompt)
            )?;
        }

        match default {
            None => write!(
                f,
                "{} {}",
                self.hint_style.apply_to("(y/n)"),
                &self.prompt_suffix
            ),
            Some(true) => write!(
                f,
                "{} {} {}",
                self.hint_style.apply_to("(y/n)"),
                &self.prompt_suffix,
                self.defaults_style.apply_to("yes")
            ),
            Some(false) => write!(
                f,
                "{} {} {}",
                self.hint_style.apply_to("(y/n)"),
                &self.prompt_suffix,
                self.defaults_style.apply_to("no")
            ),
        }
    }
    fn format_confirm_prompt_selection(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        selection: Option<bool>,
    ) -> fmt::Result {
        self.indent(f)?;
        if !prompt.is_empty() {
            write!(
                f,
                "{} {} ",
                &self.success_prefix,
                self.prompt_style.apply_to(prompt)
            )?;
        }
        let selection = selection.map(|b| if b { "yes" } else { "no" });

        match selection {
            Some(selection) => {
                write!(
                    f,
                    "{} {}",
                    &self.success_suffix,
                    self.values_style.apply_to(selection)
                )
            }
            None => {
                write!(f, "{}", &self.success_suffix)
            }
        }
    }
    fn format_input_prompt_selection(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        sel: &str,
    ) -> fmt::Result {
        self.indent(f)?;
        if !prompt.is_empty() {
            write!(
                f,
                "{} {} ",
                &self.success_prefix,
                self.prompt_style.apply_to(prompt)
            )?;
        }

        write!(
            f,
            "{} {}",
            &self.success_suffix,
            self.values_style.apply_to(sel)
        )
    }
    fn format_select_prompt_item(
        &self,
        f: &mut dyn fmt::Write,
        text: &str,
        active: bool,
    ) -> fmt::Result {
        self.indent(f)?;
        let details = if active {
            (
                &self.active_item_prefix,
                self.active_item_style.apply_to(text),
            )
        } else {
            (
                &self.inactive_item_prefix,
                self.inactive_item_style.apply_to(text),
            )
        };

        write!(f, "{} {}", details.0, details.1)
    }
}
