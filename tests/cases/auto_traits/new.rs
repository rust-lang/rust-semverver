#![feature(optin_builtin_traits)]

use std::rc::Rc;

#[allow(dead_code)]
pub struct Abc { }

impl !Send for Abc { }
impl !Sync for Abc { }

#[allow(dead_code)]
pub struct Def<A> {
    field: Rc<A>,
}

#[allow(dead_code)]
pub struct Ghi<A> {
    field: A,
}

// impl !Send for Ghi<()> { }

// causes a new impl to be found (!) -- introduce a handling for negative markers
impl<A: Clone> !Send for Ghi<A> { }
