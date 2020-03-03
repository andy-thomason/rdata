// Pubic-facing API.

use crate::{Obj, Error, Result};
use crate::obj::NA_INTEGER;

use std::str::FromStr;
use num_traits::FromPrimitive;
use std::string::ToString;

pub const NULL : () = ();
pub const TRUE : bool = true;
pub const FALSE : bool = false;

// Emulate R's c() function.
#[macro_export]
macro_rules! c {
    ($elem:expr; $n:expr) => (
        $crate::Obj::from($elem, $n).flatten()
    );
    ($($x:expr),*) => (
        $crate::Obj::from(vec![$($x),*]).flatten()
    );
}

#[macro_export]
macro_rules! structure {
    //($o:expr, ($($t:ident = $x:expr),*)) => (
    ($o:expr, $($t:ident = $x:expr),*) => {
        {
            let mut obj = $o;
            $(
                obj.add_attr(stringify!($t), $x);
            )*
            obj
        }
    };
}

#[macro_export]
macro_rules! data_frame {
    ($($t:ident = $x:expr),*) => {
        {
            let names = [$(($x),)*].to_vec();
            let values = [$(stringify!($x),)*].to_vec();
            obj::List(None, values.to_vec()).names(names.to_vec())
        }
    };
}

// Conversion
impl From<()> for Obj {
    fn from(_: ()) -> Obj {
       Obj::Nil(None)
    }
}

/// Generate a scalar integer.
impl From<i32> for Obj {
    fn from(val: i32) -> Obj {
       Obj::Int(None, vec![val])
    }
}

impl From<f64> for Obj {
    fn from(val: f64) -> Obj {
       Obj::Real(None, vec![val])
    }
}

impl From<bool> for Obj {
    fn from(val: bool) -> Obj {
       Obj::Logical(None, vec![val])
    }
}

impl From<&String> for Obj {
    fn from(val: &String) -> Obj {
       Obj::Str(None, vec![val.clone()])
    }
}

impl From<String> for Obj {
    fn from(val: String) -> Obj {
       Obj::Str(None, vec![val])
    }
}

impl From<&str> for Obj {
    fn from(val: &str) -> Obj {
       Obj::Str(None, vec![val.to_string()])
    }
}

impl From<&[&str]> for Obj {
    fn from(val: &[&str]) -> Obj {
        let strings : Vec<_> = val.iter().map(|s| s.to_string()).collect();
        Obj::Str(None, strings)
    }
}

impl From<Vec<&str>> for Obj {
    fn from(val: Vec<&str>) -> Obj {
        let strings : Vec<_> = val.iter().map(|s| s.to_string()).collect();
        Obj::Str(None, strings)
    }
}

impl From<Vec<i32>> for Obj {
    fn from(val: Vec<i32>) -> Obj {
       Obj::Int(None, val)
    }
}

impl From<Vec<f64>> for Obj {
    fn from(val: Vec<f64>) -> Obj {
       Obj::Real(None, val)
    }
}

impl From<Vec<(Obj, Obj)>> for Obj {
    fn from(val: Vec<(Obj, Obj)>) -> Obj {
       Obj::PairList(None, val)
    }
}

impl From<Vec<Obj>> for Obj {
    fn from(val: Vec<Obj>) -> Obj {
       Obj::List(None, val)
    }
}

impl From<&[u8]> for Obj {
    fn from(val: &[u8]) -> Obj {
       Obj::Raw(None, val.to_vec())
    }
}

impl PartialEq<&str> for Obj {
    fn eq(&self, rhs: &&str) -> bool {
        if let Obj::Str(_, ref val) = self {
            val.len() == 1 && &val[0] == rhs
        } else {
            false
        }
    }
}

// Allow functions to be called with an Obj without consuming it.
/*impl AsRef<Obj> for Obj {
    fn as_ref(&self) -> &Self { &self }
}

impl AsRef<Obj> for () {
    fn as_ref(&self) -> &Obj { &Obj::from(*self) }
}

impl AsRef<Obj> for bool {
    fn as_ref(&self) -> &Obj { &Obj::from(*self) }
}

impl AsRef<Obj> for f64 {
    fn as_ref(&self) -> &Obj { &Obj::from(*self) }
}

impl AsRef<Obj> for i32 {
    fn as_ref(&self) -> &Obj { &Obj::from(*self) }
}

impl AsRef<Obj> for &str {
    fn as_ref(&self) -> &Obj { &Obj::from(*self) }
}

impl AsRef<Obj> for &[u8] {
    fn as_ref(&self) -> &Obj { &Obj::from(*self) }
}*/

// https://github.com/wch/r-source/blob/trunk/src/main/coerce.c
fn f64_to<T : FromPrimitive>(val: &f64, def: T) -> T {
    T::from_f64(*val).unwrap_or(def)
}

fn i32_to<T : FromPrimitive>(val: &i32, def: T) -> T {
    T::from_i32(*val).unwrap_or(def)
}

fn str_to<T : FromStr>(val: &str, def: T) -> T {
    T::from_str(val).unwrap_or(def)
}

fn bool_to<T : FromPrimitive>(val: &bool, def: T) -> T {
    T::from_i8(if *val {1} else {0}).unwrap_or(def)
}

pub fn as_raw(obj: &Obj) -> Result<Obj> {
    match obj {
        Obj::Raw(_, _) => Ok(obj.clone()),
        Obj::Nil(_) => Ok(Obj::Raw(None, Vec::new())),
        Obj::Int(_, ref s) => Ok(Obj::Raw(None, s.iter().map(|s| i32_to(s, 0)).collect())),
        Obj::Real(_, ref s) => Ok(Obj::Raw(None, s.iter().map(|s| f64_to(s, 0)).collect())),
        Obj::Str(_, ref s) => Ok(Obj::Raw(None, s.iter().map(|s| str_to(s.as_str(), 0)).collect())),
        Obj::Logical(_, ref s)  => Ok(Obj::Raw(None, s.iter().map(|s| bool_to(s, 0)).collect())),
        _ => Err(Error::from("as_raw cannot convert from this type"))
    }
}

pub fn as_integer(obj: &Obj) -> Result<Obj> {
    match obj {
        Obj::Int(_, _) => Ok(obj.clone()),
        Obj::Nil(_) => Ok(Obj::Int(None, Vec::new())),
        Obj::Raw(_, ref s) => Ok(Obj::Int(None, s.iter().map(|s| *s as i32).collect())),
        Obj::Real(_, ref s) => Ok(Obj::Int(None, s.iter().map(|s| f64_to(s, NA_INTEGER)).collect())),
        Obj::Str(_, ref s) => Ok(Obj::Int(None, s.iter().map(|s| str_to(s.as_str(), 0)).collect())),
        Obj::Logical(_, ref s)  => Ok(Obj::Int(None, s.iter().map(|s| bool_to(s, 0)).collect())),
        _ => Err(Error::from("as_raw cannot convert from this type"))
    }
}

pub fn as_real(obj: &Obj) -> Result<Obj> {
    match obj {
        Obj::Nil(_) => Ok(obj.clone()),
        Obj::Real(_, _) => Ok(obj.clone()),
        Obj::Raw(_, ref s) => Ok(Obj::Real(None, s.iter().map(|s| *s as f64).collect())),
        Obj::Int(_, ref s) => Ok(Obj::Real(None, s.iter().map(|s| i32_to(s, 0.)).collect())),
        Obj::Str(_, ref s) => Ok(Obj::Real(None, s.iter().map(|s| str_to(s.as_str(), 0.)).collect())),
        Obj::Logical(_, ref s)  => Ok(Obj::Real(None, s.iter().map(|s| bool_to(s, 0.)).collect())),
        _ => Err(Error::from("as_raw cannot convert from this type"))
    }
}

pub fn as_character(obj: &Obj) -> Result<Obj> {
    match obj {
        Obj::Nil(_) => Ok(obj.clone()),
        Obj::Str(_, _) => Ok(obj.clone()),
        Obj::Raw(_, ref s) => Ok(Obj::Str(None, s.iter().map(|s| s.to_string()).collect())),
        Obj::Int(_, ref s) => Ok(Obj::Str(None, s.iter().map(|s| s.to_string()).collect())),
        Obj::Logical(_, ref s)  => Ok(Obj::Str(None, s.iter().map(|s| s.to_string()).collect())),
        _ => Err(Error::from("as_raw cannot convert from this type"))
    }
}

pub fn print<T: Into<Obj>>(obj: T) {
    println!("{:?}", obj.into());
}

/*pub const TRUE : Obj = NULL;

pub fn stdin() -> Obj {
    //structure!(0_i32, class=c!("terminal", "connection"))
    NULL
}

pub fn saveRDS(obj: &Obj, conn: &Obj) -> Result<()> {
    Ok(())
}

pub fn readRDS(conn: &Obj) -> Result<Obj> {
    Ok(NULL)
}*/

trait ToChars {
    fn to_chars(&self, v: &mut Vec<u8>);
}

impl ToChars for i32 {
    fn to_chars(&self, v: &mut Vec<u8>) {
        if self == &NA_INTEGER {
            v.extend(b"NA");
        } else {
            v.extend(self.to_string().as_bytes());
            v.push(b'L');
        }
    }
}

impl ToChars for f64 {
    fn to_chars(&self, v: &mut Vec<u8>) {
        match self.to_bits() {
            0x7ff00000000007a2 => {
                v.extend(b"NA");
            }
            0x7ff0000000000001 | 0x7ff8000000000000 => {
                v.extend(b"Nan");
            }
            0x7ff0000000000000 => {
                v.extend(b"Inf");
            }
            0xfff0000000000000 => {
                v.extend(b"-Inf");
            }
            _ => {
                v.extend(self.to_string().as_bytes());
            }
        }
    }
}

impl ToChars for String {
    fn to_chars(&self, v: &mut Vec<u8>) {
        v.push(b'\"');
        for ch in self.bytes() {
            // TODO: do escapes
            v.push(ch);
        }
        v.push(b'\"');
    }
}

impl ToChars for Obj {
    fn to_chars(&self, v: &mut Vec<u8>) {
        v.extend(b"list");
    }
}

impl ToChars for bool {
    fn to_chars(&self, v: &mut Vec<u8>) {
        if *self {v.extend(b"TRUE")} else {v.extend(b"FALSE")}
    }
}

fn deparse_vec<T : ToChars>(val: &[T]) -> Obj {
    let mut bytes = Vec::new();
    if val.len() == 1 {
        val[0].to_chars(&mut bytes);
    } else {
        // TODO: handle x:y
        bytes.extend(b"c(");
        if val.len() != 0 {
            val[0].to_chars(&mut bytes);
            for v in val.iter().skip(1) {
                bytes.extend(b", ");
                v.to_chars(&mut bytes);
            }
        }
        bytes.extend(b")");
    }
    unsafe { Obj::from(String::from_utf8_unchecked(bytes)) }
}

fn deparse_pairlist(label: &str, _val: &Vec<(Obj, Obj)>) -> Obj {
    let mut bytes = Vec::new();
    bytes.extend(label.as_bytes());
    unsafe { Obj::from(String::from_utf8_unchecked(bytes)) }
}

pub fn deparse<T : Into<Obj>>(obj: T) -> Obj {
    match obj.into() {
        Obj::Sym(_, ref val) => Obj::string(val.name.as_str()),
        Obj::Env(_, _) => Obj::string("<environment>"),
        Obj::PairList(_, ref val) => deparse_pairlist("pairlist", val),
        Obj::Closure(_, ref val) => deparse_pairlist("closure", val),
        Obj::Promise(_, ref val) => deparse_pairlist("promise", val),
        Obj::Lang(_, ref val) => deparse_pairlist("lang", val),
        Obj::Dot(_, _) => Obj::string("..."),
        Obj::Special(_, ref val) => Obj::string(val),
        Obj::Builtin(_, ref val) => Obj::string(val),
        Obj::Char(_, ref val) => Obj::string(val),
        Obj::Logical(_, ref val) => deparse_vec(val),
        Obj::Int(_, ref val) => deparse_vec(val),
        Obj::Real(_, ref val) => deparse_vec(val),
        Obj::Cplx(_, _) => Obj::string("???"),
        Obj::Str(_, ref val) => deparse_vec(val),
        Obj::List(_, ref val) => deparse_vec(val),
        Obj::Expr(_, ref _val) => Obj::string("???"),
        Obj::Nil(_) => Obj::string("NULL"),
        Obj::Global(_) => Obj::string("globalenv()"),
        Obj::Unbound(_) => Obj::string("unbound()"),
        Obj::MissingArg(_) => Obj::string("missingarg()"),
        Obj::BaseNamespace(_) => Obj::string("basenamespace()"),
        Obj::EmptyEnv(_) => Obj::string("emptyenv()"),
        Obj::BaseEnv(_) => Obj::string("baseenv()"),
        _ => Obj::string("???"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deparse() -> Result<()> {
        // Call R and deparse the result. Compare this with the expected value.
        assert_eq!(deparse(NULL), "NULL");
        assert_eq!(deparse(TRUE), "TRUE");
        assert_eq!(deparse(FALSE), "FALSE");
        assert_eq!(deparse(()), "NULL");
        assert_eq!(deparse(1.), "1");
        assert_eq!(deparse(1), "1L");
        assert_eq!(deparse("xyz"), "\"xyz\"");
        assert_eq!(deparse(c!("abc", "xyz")), "c(\"abc\", \"xyz\")");
        assert_eq!(deparse(c!(1., 2.)), "c(1, 2)");
        assert_eq!(deparse(c!(1, 3)), "c(1L, 3L)");
        assert_eq!(deparse(true), "TRUE");
        assert_eq!(deparse(false), "FALSE");
        //assert_eq!(deparse(b"hello" as &[u8]), "as.raw(c(0x68, 0x65, 0x6c, 0x6c, 0x6f))");
        //assert_eq!(deparse(as_raw(c!(0x68, 0x65, 0x6c, 0x6c, 0x6f))?), "as.raw(c(0x68, 0x65, 0x6c, 0x6c, 0x6f))");
        //assert_eq!(deparse(structure!(c!(1., 2., 3.), x=4., y="y")), "structure(c(1, 2, 3), x = 4, y = \"y\")");
        Ok(())
    }
}
