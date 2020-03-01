// Pubic-facing API.

use crate::{Obj, Error, Result};
use crate::obj::NA_INTEGER;

use std::str::FromStr;
use num_traits::FromPrimitive;

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

pub fn as_raw<T : AsRef<Obj>>(obj: T) -> Result<Obj> {
    let obj = obj.as_ref();
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
