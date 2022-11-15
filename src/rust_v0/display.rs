//! Pretty printing demangled symbol names.

use crate::rust_v0::{
    Abi, BasicType, Const, ConstFields, DynBounds, DynTrait, DynTraitAssocBinding, FnSig, GenericArg, Path, Type,
};
use std::{any, fmt};

/// Denote the style for displaying the symbol.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Style {
    /// Omit enclosing namespaces to get a shorter name.
    Short,
    /// Omit crate hashes and const value types. This matches rustc-demangle’s `{}` format.
    Normal,
    /// Show crate hashes and const value types. This matches rustc-demangle’s `{:#}` format. Note that even with this
    /// style, impl paths are still omitted.
    Long,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum DemangleNodeType {
    /// An identifier has been entered.
    Identifier,
    /// A namespace has been entered.
    Namespace,
    /// Additional values may be added in the future. Use a
    /// _ pattern for compatibility.
    __NonExhaustive,
}

/// Sink for demanged text that reports syntactic structure.
pub trait DemangleWrite {
    /// Called when we are entering the scope of some AST node.
    fn push_demangle_node(&mut self, _: DemangleNodeType) {}
    /// Same as `fmt::Write::write_str`.
    fn write_str(&mut self, s: &str) -> fmt::Result;
    /// Same as `fmt::write::write_fmt`.
    fn write_fmt(&mut self, args: fmt::Arguments<'_>) -> fmt::Result {
        if let Some(s) = args.as_str() {
            self.write_str(s)
        } else {
            self.write_str(&args.to_string())
        }
    }
    /// Called when we are exiting the scope of some AST node for
    /// which `push_demangle_node` was called.
    fn pop_demangle_node(&mut self) {}
}

impl<W: fmt::Write> DemangleWrite for W {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        fmt::Write::write_str(self, s)
    }
    fn write_fmt(&mut self, args: fmt::Arguments<'_>) -> fmt::Result {
        fmt::Write::write_fmt(self, args)
    }
}

pub fn display_fn(f: impl Fn(&mut fmt::Formatter) -> fmt::Result) -> impl fmt::Display {
    struct Wrapper<F>(F);

    impl<F: Fn(&mut fmt::Formatter) -> fmt::Result> fmt::Display for Wrapper<F> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            self.0(f)
        }
    }

    Wrapper(f)
}

fn write_separated_list<T>(
    values: impl IntoIterator<Item = T>,
    out: &mut dyn DemangleWrite,
    mut f: impl FnMut(T, &mut dyn DemangleWrite) -> fmt::Result,
    separator: &str,
) -> fmt::Result {
    let mut iter = values.into_iter();

    if let Some(first) = iter.next() {
        f(first, out)?;

        for value in iter {
            out.write_str(separator)?;
            f(value, out)?;
        }
    }

    Ok(())
}

pub fn write_path(
    path: &Path,
    out: &mut dyn DemangleWrite,
    style: Style,
    bound_lifetime_depth: u64,
    in_value: bool,
) -> fmt::Result {
    match path {
        Path::CrateRoot(identifier) => {
            out.push_demangle_node(DemangleNodeType::Identifier);
            match style {
                Style::Short | Style::Normal => out.write_str(&identifier.name),
                Style::Long => {
                    write!(out, "{}[{:x}]", identifier.name, identifier.disambiguator)
                }
            }?;
            out.pop_demangle_node();
            Ok(())
        },
        Path::InherentImpl { type_, .. } => {
            out.write_str("<")?;
            write_type(type_, out, style, bound_lifetime_depth)?;
            out.write_str(">")
        }
        Path::TraitImpl { type_, trait_, .. } | Path::TraitDefinition { type_, trait_ } => {
            out.write_str("<")?;
            write_type(type_, out, style, bound_lifetime_depth)?;
            out.write_str(" as ")?;
            write_path(trait_, out, style, bound_lifetime_depth, false)?;
            out.write_str(">")
        }
        Path::Nested {
            namespace,
            path,
            identifier,
        } => match namespace {
            b'A'..=b'Z' => {
                out.push_demangle_node(DemangleNodeType::Namespace);
                write_path(path, out, style, bound_lifetime_depth, in_value)?;

                out.push_demangle_node(DemangleNodeType::Identifier);
                out.write_str("::{")?;

                match namespace {
                    b'C' => out.write_str("closure")?,
                    b'S' => out.write_str("shim")?,
                    _ => write!(out, "{}", char::from(*namespace))?,
                }

                if !identifier.name.is_empty() {
                    write!(out, ":{}", identifier.name)?;
                }

                write!(out, "#{}}}", identifier.disambiguator)?;
                out.pop_demangle_node();
                out.pop_demangle_node();
                Ok(())
            }
            b'a'..=b'z' => {
                if matches!(style, Style::Normal | Style::Long)
                    || matches!(
                        path.as_ref(),
                        Path::InherentImpl { .. }
                            | Path::TraitImpl { .. }
                            | Path::TraitDefinition { .. }
                            | Path::Generic { .. }
                    )
                {
                    out.push_demangle_node(DemangleNodeType::Namespace);
                    write_path(path, out, style, bound_lifetime_depth, in_value)?;

                    if !identifier.name.is_empty() {
                        out.push_demangle_node(DemangleNodeType::Identifier);
                        write!(out, "::{}", identifier.name)?;
                        out.pop_demangle_node();
                    }
                    out.pop_demangle_node();
                } else if identifier.name.is_empty() {
                    out.push_demangle_node(DemangleNodeType::Namespace);
                    write_path(path, out, style, bound_lifetime_depth, in_value)?;
                    out.pop_demangle_node();
                } else {
                    out.push_demangle_node(DemangleNodeType::Identifier);
                    write!(out, "{}", identifier.name)?;
                    out.pop_demangle_node();
                }
                Ok(())
            }
            _ => Err(fmt::Error),
        },
        Path::Generic { path, generic_args } => {
            write_path(path, out, style, bound_lifetime_depth, in_value)?;

            if in_value {
                out.write_str("::")?;
            }

            out.write_str("<")?;
            write_separated_list(
                generic_args,
                out,
                |generic_arg, out| write_generic_arg(generic_arg, out, style, bound_lifetime_depth),
                ", ",
            )?;
            out.write_str(">")
        }
    }
}

fn write_lifetime(lifetime: u64, out: &mut dyn DemangleWrite, bound_lifetime_depth: u64) -> fmt::Result {
    out.write_str("'")?;

    if lifetime == 0 {
        out.write_str("_")
    } else if let Some(depth) = bound_lifetime_depth.checked_sub(lifetime) {
        if depth < 26 {
            write!(out, "{}", char::from(b'a' + u8::try_from(depth).unwrap()))
        } else {
            write!(out, "_{}", depth)
        }
    } else {
        Err(fmt::Error)
    }
}

pub fn write_generic_arg(
    generic_arg: &GenericArg,
    out: &mut dyn DemangleWrite,
    style: Style,
    bound_lifetime_depth: u64,
) -> fmt::Result {
    match generic_arg {
        GenericArg::Lifetime(lifetime) => write_lifetime(*lifetime, out, bound_lifetime_depth),
        GenericArg::Type(type_) => write_type(type_, out, style, bound_lifetime_depth),
        GenericArg::Const(const_) => write_const(const_, out, style, bound_lifetime_depth, false),
    }
}

fn write_binder(bound_lifetimes: u64, out: &mut dyn DemangleWrite, bound_lifetime_depth: u64) -> fmt::Result {
    out.write_str("for<")?;
    write_separated_list(
        (1..=bound_lifetimes).rev(),
        out,
        |i, out| write_lifetime(i, out, bound_lifetime_depth + bound_lifetimes),
        ", ",
    )?;
    out.write_str(">")
}

pub fn write_type(type_: &Type, out: &mut dyn DemangleWrite, style: Style, bound_lifetime_depth: u64) -> fmt::Result {
    match type_ {
        Type::Basic(basic_type) => write_basic_type(*basic_type, out),
        Type::Named(path) => write_path(path, out, style, bound_lifetime_depth, false),
        Type::Array(type_, length) => {
            out.write_str("[")?;
            write_type(type_, out, style, bound_lifetime_depth)?;
            out.write_str("; ")?;
            write_const(length, out, style, bound_lifetime_depth, true)?;
            out.write_str("]")
        }
        Type::Slice(type_) => {
            out.write_str("[")?;
            write_type(type_, out, style, bound_lifetime_depth)?;
            out.write_str("]")
        }
        Type::Tuple(tuple_types) => {
            out.write_str("(")?;
            write_separated_list(
                tuple_types,
                out,
                |type_, out| write_type(type_, out, style, bound_lifetime_depth),
                ", ",
            )?;

            if tuple_types.len() == 1 {
                out.write_str(",")?;
            }

            out.write_str(")")
        }
        Type::Ref { lifetime, type_ } => {
            out.write_str("&")?;

            if *lifetime != 0 {
                write_lifetime(*lifetime, out, bound_lifetime_depth)?;
                out.write_str(" ")?;
            }

            write_type(type_, out, style, bound_lifetime_depth)
        }
        Type::RefMut { lifetime, type_ } => {
            out.write_str("&")?;

            if *lifetime != 0 {
                write_lifetime(*lifetime, out, bound_lifetime_depth)?;
                out.write_str(" ")?;
            }

            out.write_str("mut ")?;
            write_type(type_, out, style, bound_lifetime_depth)
        }
        Type::PtrConst(type_) => {
            out.write_str("*const ")?;
            write_type(type_, out, style, bound_lifetime_depth)
        }
        Type::PtrMut(type_) => {
            out.write_str("*mut ")?;
            write_type(type_, out, style, bound_lifetime_depth)
        }
        Type::Fn(fn_sig) => write_fn_sig(fn_sig, out, style, bound_lifetime_depth),
        Type::DynTrait { dyn_bounds, lifetime } => {
            write_dyn_bounds(dyn_bounds, out, style, bound_lifetime_depth)?;

            if *lifetime == 0 {
                Ok(())
            } else {
                out.write_str(" + ")?;
                write_lifetime(*lifetime, out, bound_lifetime_depth)
            }
        }
    }
}

pub fn write_basic_type(basic_type: BasicType, out: &mut dyn DemangleWrite) -> fmt::Result {
    out.write_str(match basic_type {
        BasicType::I8 => "i8",
        BasicType::Bool => "bool",
        BasicType::Char => "char",
        BasicType::F64 => "f64",
        BasicType::Str => "str",
        BasicType::F32 => "f32",
        BasicType::U8 => "u8",
        BasicType::Isize => "isize",
        BasicType::Usize => "usize",
        BasicType::I32 => "i32",
        BasicType::U32 => "u32",
        BasicType::I128 => "i128",
        BasicType::U128 => "u128",
        BasicType::I16 => "i16",
        BasicType::U16 => "u16",
        BasicType::Unit => "()",
        BasicType::Ellipsis => "...",
        BasicType::I64 => "i64",
        BasicType::U64 => "u64",
        BasicType::Never => "!",
        BasicType::Placeholder => "_",
    })
}

pub fn write_fn_sig(
    fn_sig: &FnSig,
    out: &mut dyn DemangleWrite,
    style: Style,
    bound_lifetime_depth: u64,
) -> fmt::Result {
    if fn_sig.bound_lifetimes != 0 {
        write_binder(fn_sig.bound_lifetimes, out, bound_lifetime_depth)?;
        out.write_str(" ")?;
    }

    let bound_lifetime_depth = bound_lifetime_depth + fn_sig.bound_lifetimes;

    if fn_sig.is_unsafe {
        out.write_str("unsafe ")?;
    }

    if let Some(abi) = &fn_sig.abi {
        out.write_str("extern ")?;
        write_abi(abi, out)?;
        out.write_str(" ")?;
    }

    out.write_str("fn(")?;
    write_separated_list(
        &fn_sig.argument_types,
        out,
        |type_, out| write_type(type_, out, style, bound_lifetime_depth),
        ", ",
    )?;
    out.write_str(")")?;

    if let Type::Basic(BasicType::Unit) = fn_sig.return_type.as_ref() {
        Ok(())
    } else {
        out.write_str(" -> ")?;
        write_type(&fn_sig.return_type, out, style, bound_lifetime_depth)
    }
}

fn write_abi(abi: &Abi, out: &mut dyn DemangleWrite) -> fmt::Result {
    out.write_str("\"")?;

    match abi {
        Abi::C => out.write_str("C")?,
        Abi::Named(name) => {
            let mut iter = name.split('_');

            out.write_str(iter.next().unwrap())?;

            for item in iter {
                write!(out, "-{}", item)?;
            }
        }
    }

    out.write_str("\"")
}

fn write_dyn_bounds(
    dyn_bounds: &DynBounds,
    out: &mut dyn DemangleWrite,
    style: Style,
    bound_lifetime_depth: u64,
) -> fmt::Result {
    out.write_str("dyn ")?;

    if dyn_bounds.bound_lifetimes != 0 {
        write_binder(dyn_bounds.bound_lifetimes, out, bound_lifetime_depth)?;
        out.write_str(" ")?;
    }

    let bound_lifetime_depth = bound_lifetime_depth + dyn_bounds.bound_lifetimes;

    write_separated_list(
        dyn_bounds.dyn_traits.iter(),
        out,
        |dyn_trait, out| write_dyn_trait(dyn_trait, out, style, bound_lifetime_depth),
        " + ",
    )
}

fn write_dyn_trait(
    dyn_trait: &DynTrait,
    out: &mut dyn DemangleWrite,
    style: Style,
    bound_lifetime_depth: u64,
) -> fmt::Result {
    if dyn_trait.dyn_trait_assoc_bindings.is_empty() {
        write_path(&dyn_trait.path, out, style, bound_lifetime_depth, false)
    } else if let Path::Generic { path, generic_args } = dyn_trait.path.as_ref() {
        write_path(path, out, style, bound_lifetime_depth, false)?;
        write!(out, "<")?;
        write_separated_list(
            generic_args
                .iter()
                .map(Ok)
                .chain(dyn_trait.dyn_trait_assoc_bindings.iter().map(Err)),
            out,
            |value, out| match value {
                Ok(generic_arg) => write_generic_arg(generic_arg, out, style, bound_lifetime_depth),
                Err(dyn_trait_assoc_binding) => {
                    write_dyn_trait_assoc_binding(dyn_trait_assoc_binding, out, style, bound_lifetime_depth)
                }
            },
            ", ",
        )?;
        write!(out, ">")
    } else {
        write_path(&dyn_trait.path, out, style, bound_lifetime_depth, false)?;
        write!(out, "<")?;
        write_separated_list(
            dyn_trait.dyn_trait_assoc_bindings.iter(),
            out,
            |dyn_trait_assoc_binding, out| {
                write_dyn_trait_assoc_binding(dyn_trait_assoc_binding, out, style, bound_lifetime_depth)
            },
            ", ",
        )?;
        write!(out, ">")
    }
}

fn write_dyn_trait_assoc_binding(
    dyn_trait_assoc_binding: &DynTraitAssocBinding,
    out: &mut dyn DemangleWrite,
    style: Style,
    bound_lifetime_depth: u64,
) -> fmt::Result {
    write!(out, "{} = ", dyn_trait_assoc_binding.name)?;
    write_type(&dyn_trait_assoc_binding.type_, out, style, bound_lifetime_depth)
}

fn write_integer<T: fmt::Display>(value: T, out: &mut dyn DemangleWrite, style: Style) -> fmt::Result {
    write!(out, "{}", value)?;

    if matches!(style, Style::Long) {
        out.write_str(any::type_name::<T>())
    } else {
        Ok(())
    }
}

pub fn write_const(
    const_: &Const,
    out: &mut dyn DemangleWrite,
    style: Style,
    bound_lifetime_depth: u64,
    in_value: bool,
) -> fmt::Result {
    match *const_ {
        Const::I8(value) => write_integer(value, out, style),
        Const::U8(value) => write_integer(value, out, style),
        Const::Isize(value) => write_integer(value, out, style),
        Const::Usize(value) => write_integer(value, out, style),
        Const::I32(value) => write_integer(value, out, style),
        Const::U32(value) => write_integer(value, out, style),
        Const::I128(value) => write_integer(value, out, style),
        Const::U128(value) => write_integer(value, out, style),
        Const::I16(value) => write_integer(value, out, style),
        Const::U16(value) => write_integer(value, out, style),
        Const::I64(value) => write_integer(value, out, style),
        Const::U64(value) => write_integer(value, out, style),
        Const::Bool(value) => write!(out, "{}", value),
        Const::Char(value) => write!(out, "{:?}", value),
        Const::Str(ref value) => {
            if in_value {
                write!(out, "*{:?}", value)
            } else {
                write!(out, "{{*{:?}}}", value)
            }
        }
        Const::Ref(ref value) => {
            if let Const::Str(value) = value.as_ref() {
                write!(out, "{:?}", value)
            } else if in_value {
                out.write_str("&")?;
                write_const(value, out, style, bound_lifetime_depth, true)
            } else {
                out.write_str("{&")?;
                write_const(value, out, style, bound_lifetime_depth, true)?;
                out.write_str("}")
            }
        }
        Const::RefMut(ref value) => {
            if in_value {
                out.write_str("&mut ")?;
            } else {
                out.write_str("{&mut ")?;
            }
            write_const(value, out, style, bound_lifetime_depth, true)?;
            if !in_value {
                out.write_str("}")?;
            }
            Ok(())
        }
        Const::Array(ref items) => {
            if in_value {
                out.write_str("[")?;
            } else {
                out.write_str("{[")?;
            }
            write_separated_list(
                items,
                out,
                |item, out| write_const(item, out, style, bound_lifetime_depth, true),
                ", ",
            )?;

            if in_value {
                out.write_str("]")
            } else {
                out.write_str("]}")
            }
        }
        Const::Tuple(ref items) => {
            if in_value {
                out.write_str("(")?;
            } else {
                out.write_str("{(")?;
            }

            write_separated_list(
                items,
                out,
                |item, out| write_const(item, out, style, bound_lifetime_depth, true),
                ", ",
            )?;

            if in_value {
                out.write_str(if items.len() == 1 { ",)" } else { ")" })
            } else {
                out.write_str(if items.len() == 1 { ",)}" } else { ")}" })
            }
        }
        Const::NamedStruct { ref path, ref fields } => {
            if !in_value {
                out.write_str("{")?;
            }
            write_path(path, out, style, bound_lifetime_depth, true)?;
            write_const_fields(fields, out, style, bound_lifetime_depth)?;

            if !in_value {
                out.write_str("}")?;
            }
            Ok(())
        }
        Const::Placeholder => out.write_str("_"),
    }
}

fn write_const_fields(
    fields: &ConstFields,
    out: &mut dyn DemangleWrite,
    style: Style,
    bound_lifetime_depth: u64,
) -> fmt::Result {
    match fields {
        ConstFields::Unit => Ok(()),
        ConstFields::Tuple(fields) => {
            out.write_str("(")?;
            write_separated_list(
                fields,
                out,
                |field, out| write_const(field, out, style, bound_lifetime_depth, true),
                ", ",
            )?;
            out.write_str(")")
        }
        ConstFields::Struct(fields) => {
            if fields.is_empty() {
                // Matches the behavior of `rustc-demangle`.
                out.write_str(" {  }")
            } else {
                out.write_str(" { ")?;
                write_separated_list(
                    fields.iter(),
                    out,
                    |(name, value), out| {
                        write!(out, "{}", name)?;
                        out.write_str(": ")?;
                        write_const(value, out, style, bound_lifetime_depth, true)
                    },
                    ", ",
                )?;
                out.write_str(" }")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Style;
    use crate::rust_v0::Symbol;
    use std::fmt::Write;

    #[test]
    fn test_display_path() {
        let test_cases = [(
            "_RINvCsd5QWgxammnl_7example3fooNcNtINtNtCs454gRYH7d6L_4core6result6ResultllE2Ok0EB2_",
            (
                "foo::<Result<i32, i32>::Ok>",
                "example::foo::<core::result::Result<i32, i32>::Ok>",
                "example[9884ce86676676d1]::foo::<core[2f8af133219d6c11]::result::Result<i32, i32>::Ok>",
            ),
        )];

        let mut buffer = String::new();

        for (symbol, expected) in test_cases {
            let symbol = Symbol::parse_from_str(symbol).unwrap().0;

            write!(buffer, "{}", symbol.display(Style::Short)).unwrap();

            let length_1 = buffer.len();

            write!(buffer, "{}", symbol.display(Style::Normal)).unwrap();

            let length_2 = buffer.len();

            write!(buffer, "{}", symbol.display(Style::Long)).unwrap();

            assert_eq!(
                (&buffer[..length_1], &buffer[length_1..length_2], &buffer[length_2..]),
                expected
            );

            buffer.clear();
        }
    }

    #[test]
    fn test_display_lifetime() {
        #[track_caller]
        fn check(lifetime: u64, bound_lifetime_depth: u64, expected: &str) {
            assert_eq!(
                super::display_fn(move |f| { super::write_lifetime(lifetime, f, bound_lifetime_depth) }).to_string(),
                expected
            );
        }

        check(0, 0, "'_");
        check(0, 1, "'_");
        check(0, 2, "'_");

        check(1, 1, "'a");
        check(1, 2, "'b");
        check(1, 3, "'c");

        check(2, 2, "'a");
        check(2, 3, "'b");
        check(2, 4, "'c");
    }

    #[test]
    fn test_display_binder() {
        #[track_caller]
        fn check(bound_lifetimes: u64, bound_lifetime_depth: u64, expected: &str) {
            assert_eq!(
                super::display_fn(move |f| { super::write_binder(bound_lifetimes, f, bound_lifetime_depth) })
                    .to_string(),
                expected
            );
        }

        check(0, 0, "for<>");
        check(0, 1, "for<>");
        check(0, 2, "for<>");

        check(1, 0, "for<'a>");
        check(1, 1, "for<'b>");
        check(1, 2, "for<'c>");

        check(2, 0, "for<'a, 'b>");
        check(2, 1, "for<'b, 'c>");
        check(2, 2, "for<'c, 'd>");
    }
}
