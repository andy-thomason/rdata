// Pubic-facing API.

use crate::{Obj, Error, Result, do_typed};
use crate::obj::{ArrayRef, ToChars, Type};

use std::str::FromStr;
use num_traits::{ToPrimitive};
//use std::string::ToString;

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

fn str_to<T : FromStr>(val: &str, def: T) -> T {
    T::from_str(val).unwrap_or(def)
}

trait ToI64 {
    fn to_i64(&self) -> i64;
}

impl ToI64 for bool { fn to_i64(&self) -> i64 { if *self {1} else {0} } }
impl ToI64 for i8 { fn to_i64(&self) -> i64 { *self as i64 } }
impl ToI64 for i16 { fn to_i64(&self) -> i64 { *self as i64 } }
impl ToI64 for i32 { fn to_i64(&self) -> i64 { *self as i64 } }
impl ToI64 for i64 { fn to_i64(&self) -> i64 { *self as i64 } }
impl ToI64 for u8 { fn to_i64(&self) -> i64 { *self as i64 } }
impl ToI64 for u16 { fn to_i64(&self) -> i64 { *self as i64 } }
impl ToI64 for u32 { fn to_i64(&self) -> i64 { *self as i64 } }
impl ToI64 for u64 { fn to_i64(&self) -> i64 { *self as i64 } }
impl ToI64 for f32 { fn to_i64(&self) -> i64 { *self as i64 } }
impl ToI64 for f64 { fn to_i64(&self) -> i64 { *self as i64 } }

fn ary_to_u8<T : ToI64>(ary: &ArrayRef) -> Result<Obj> {
    if let Some(s) = ary.as_slice::<T>() {
        let ar : Vec<_> = s.iter().map(|s| s.to_i64().to_u8().unwrap_or(0_u8)).collect();
        Ok(Obj::from(ar))
    } else {
        Err(Error::from("cannot convert to u8"))
    }
}

pub fn as_raw(obj: &Obj) -> Result<Obj> {
    match obj {
        Obj::Nil(_) => Ok(Obj::from(vec![0_u8; 0])),
        Obj::Ary(_, ref s) => do_typed!(ary_to_u8, s),
        Obj::Str(_, ref s) => Ok(s.iter().map(|s| str_to::<u8>(s.as_str(), 0)).collect::<Vec<u8>>().into()),
        _ => Err(Error::from("as_raw cannot convert from this type"))
    }
}

pub fn as_integer(obj: &Obj) -> Result<Obj> {
    match obj {
        /*Obj::Ary(_, _) => do_typed!(s, ary_to_i32),
        Obj::Nil(_) => Ok(Obj::Ary(None, FromVec::new())),
        Obj::Raw(_, ref s) => Ok(Obj::Int(None, s.iter().map(|s| *s as i32).collect())),
        Obj::Real(_, ref s) => Ok(Obj::Int(None, s.iter().map(|s| f64_to(s, NA_INTEGER)).collect())),
        Obj::Str(_, ref s) => Ok(Obj::Int(None, s.iter().map(|s| str_to(s.as_str(), 0)).collect())),
        Obj::Logical(_, ref s)  => Ok(Obj::Int(None, s.iter().map(|s| bool_to(s, 0)).collect())),*/
        _ => Err(Error::from("as_raw cannot convert from this type"))
    }
}

pub fn as_real(obj: &Obj) -> Result<Obj> {
    match obj {
        Obj::Nil(_) => Ok(obj.clone()),
        /*Obj::Real(_, _) => Ok(obj.clone()),
        Obj::Raw(_, ref s) => Ok(Obj::Real(None, s.iter().map(|s| *s as f64).collect())),
        Obj::Int(_, ref s) => Ok(Obj::Real(None, s.iter().map(|s| i32_to(s, 0.)).collect())),
        Obj::Str(_, ref s) => Ok(Obj::Real(None, s.iter().map(|s| str_to(s.as_str(), 0.)).collect())),
        Obj::Logical(_, ref s)  => Ok(Obj::Real(None, s.iter().map(|s| bool_to(s, 0.)).collect())),*/
        _ => Err(Error::from("as_raw cannot convert from this type"))
    }
}

pub fn as_character(obj: &Obj) -> Result<Obj> {
    match obj {
        /*Obj::Nil(_) => Ok(obj.clone()),
        Obj::Str(_, _) => Ok(obj.clone()),
        Obj::Raw(_, ref s) => Ok(Obj::Str(None, s.iter().map(|s| s.to_string()).collect())),
        Obj::Int(_, ref s) => Ok(Obj::Str(None, s.iter().map(|s| s.to_string()).collect())),
        Obj::Logical(_, ref s)  => Ok(Obj::Str(None, s.iter().map(|s| s.to_string()).collect())),*/
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

fn deparse_ary<T : ToChars>(ary: &ArrayRef) -> Obj {
    let mut bytes = Vec::new();
    let val = ary.as_slice::<T>();
    if let Some(val) = val {
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
    }
    Obj::from(unsafe { String::from_utf8_unchecked(bytes) })
}

fn deparse_pairlist(label: &str, _val: &Vec<(Obj, Obj)>) -> Obj {
    let mut bytes = Vec::new();
    bytes.extend(label.as_bytes());
    unsafe { Obj::from(String::from_utf8_unchecked(bytes)) }
}

pub fn deparse<T : Into<Obj>>(obj: T) -> Obj {
    match obj.into() {
        Obj::Sym(_, ref val) => Obj::from(val.name.as_str()),
        Obj::Env(_, _) => Obj::from("<environment>"),
        Obj::PairList(_, ref val) => deparse_pairlist("pairlist", val),
        Obj::Closure(_, ref val) => deparse_pairlist("closure", val),
        Obj::Promise(_, ref val) => deparse_pairlist("promise", val),
        Obj::Lang(_, ref val) => deparse_pairlist("lang", val),
        Obj::Dot(_, _) => Obj::from("..."),
        Obj::Special(_, ref val) => Obj::from(val),
        Obj::Builtin(_, ref val) => Obj::from(val),
        Obj::Char(_, ref val) => Obj::from(val),
        Obj::Ary(_, ref val) => do_typed!(deparse_ary, val),
        Obj::Str(_, ref val) => deparse_vec(val),
        Obj::List(_, ref val) => deparse_vec(val),
        Obj::Expr(_, ref _val) => Obj::from("???"),
        Obj::Nil(_) => Obj::from("NULL"),
        Obj::Global(_) => Obj::from("globalenv()"),
        Obj::Unbound(_) => Obj::from("unbound()"),
        Obj::MissingArg(_) => Obj::from("missingarg()"),
        Obj::BaseNamespace(_) => Obj::from("basenamespace()"),
        Obj::EmptyEnv(_) => Obj::from("emptyenv()"),
        Obj::BaseEnv(_) => Obj::from("baseenv()"),
        //_ => Obj::from("???"),
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
