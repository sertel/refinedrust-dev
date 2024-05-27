#![feature(box_patterns)]
#![feature(let_chains)]
#![allow(clippy::pub_use)]

pub mod code;
pub mod coq;
pub mod specs;

pub use code::*;
pub use specs::*;

pub(crate) const BASE_INDENT: &str = "  ";

fn make_indent(i: usize) -> String {
    " ".repeat(i)
}

/// Extend the `core::fmt::Display` trait to display a collection separated by a separator.
///
/// The macro can take an optional fourth argument to customise the format string (default: `"{}"`).
/// This fourth argument can also be a closure that takes an element from the collection and returns the
/// formatted string.
#[macro_export]
macro_rules! display_list {
    ($collection:expr, $separator:expr) => {
        $crate::display_list!($collection, $separator, "{}")
    };
    ($collection:expr, $separator:expr, $pattern:literal) => {
        $crate::display_list!($collection, $separator, |e| format!($pattern, e))
    };
    ($collection:expr, $separator:expr, $fmt:expr) => {
        $collection.into_iter().map($fmt).collect::<Vec<_>>().join($separator)
    };
}

/// Extend the `String::push_str` method to push a collection separated by a separator.
///
/// The macro can take an optional fourth argument to customise the format string (default: `"{}"`).
/// This fourth argument can also be a closure that takes an element from the collection and returns the
/// formatted string.
#[macro_export]
macro_rules! push_str_list {
    ($s:ident, $collection:expr, $separator:expr) => {
        $crate::push_str_list!($s, $collection, $separator, "{}")
    };
    ($s:ident, $collection:expr, $separator:expr, $pattern:literal) => {
        $crate::push_str_list!($s, $collection, $separator, |e| format!($pattern, e))
    };
    ($s:ident, $collection:expr, $separator:expr, $fmt:expr) => {
        $s.push_str(&$crate::display_list!($collection, $separator, $fmt))
    };
}

/// Extend the `write!` macro to write a collection separated by a separator.
///
/// The macro can take an optional fourth argument to customise the format string (default: `"{}"`).
/// This fourth argument can also be a closure that takes an element from the collection and returns the
/// formatted string.
#[macro_export]
macro_rules! write_list {
    ($f:ident, $collection:expr, $separator:expr) => {
        $crate::write_list!($f, $collection, $separator, "{}")
    };
    ($f:ident, $collection:expr, $separator:expr, $pattern:literal) => {
        $crate::write_list!($f, $collection, $separator, |e| format!($pattern, e))
    };
    ($f:ident, $collection:expr, $separator:expr, $fmt:expr) => {
        write!($f, "{}", $crate::display_list!($collection, $separator, $fmt))
    };
}

#[cfg(test)]
mod tests {
    use std::fmt::Write;

    #[test]
    fn display_list_default() {
        let out = display_list!(vec!["10", "20"], "; ");
        assert_eq!(out, "10; 20");
    }

    #[test]
    fn display_list_pattern() {
        let out = display_list!(vec!["10", "20"], "; ", "'{}'");
        assert_eq!(out, "'10'; '20'");
    }

    #[test]
    fn display_list_format() {
        let out = display_list!(vec![("x", "10"), ("y", "20")], "; ", |(l, v)| format!("{l}: {v}"));
        assert_eq!(out, "x: 10; y: 20");
    }

    #[test]
    fn push_str_list_default() {
        let mut out = String::new();
        push_str_list!(out, vec!["10", "20"], "; ");
        assert_eq!(out, "10; 20");
    }

    #[test]
    fn push_str_list_pattern() {
        let mut out = String::new();
        push_str_list!(out, vec!["10", "20"], "; ", "'{}'");
        assert_eq!(out, "'10'; '20'");
    }

    #[test]
    fn push_str_list_format() {
        let mut out = String::new();
        push_str_list!(out, vec![("x", "10"), ("y", "20")], "; ", |(l, v)| format!("{l}: {v}"));
        assert_eq!(out, "x: 10; y: 20");
    }

    #[test]
    fn write_list_default() {
        let mut out = String::new();
        write_list!(out, vec!["10", "20"], "; ").unwrap();
        assert_eq!(out, "10; 20");
    }

    #[test]
    fn write_list_pattern() {
        let mut out = String::new();
        write_list!(out, vec!["10", "20"], "; ", "'{}'").unwrap();
        assert_eq!(out, "'10'; '20'");
    }

    #[test]
    fn write_list_format() {
        let mut out = String::new();
        write_list!(out, vec![("x", "10"), ("y", "20")], "; ", |(l, v)| format!("{l}: {v}")).unwrap();
        assert_eq!(out, "x: 10; y: 20");
    }
}
