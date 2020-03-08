#![feature(rustc_private)]
#![allow(clippy::similar_names)]
#![allow(clippy::single_match_else)]
#![allow(clippy::too_many_lines)]
#![deny(warnings)]
extern crate rustc;
extern crate rustc_ast;
extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_mir;
extern crate rustc_span;

mod changes;
mod mapping;
mod mismatch;
mod translate;
mod traverse;
mod typeck;

pub use self::traverse::{run_analysis, run_traversal};
