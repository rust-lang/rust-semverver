//! The utility module responsible for holding code to do boring chores.

use std::mem;

use rustc::hir::{self, def};
use rustc::hir::def_id::{CRATE_DEF_INDEX, DefId};
use rustc::ty::TyCtxt;

use rustc_data_structures::sync::Lrc;

// Start of code copied from rust-clippy

pub fn get_trait_def_id(tcx: &TyCtxt, path: &[&str], use_local: bool) -> Option<DefId> {
    if use_local {
        path_to_def_local(tcx, path)
    } else {
        path_to_def(tcx, path)
    }
}

fn path_to_def_local(tcx: &TyCtxt, path: &[&str]) -> Option<DefId> {
    let krate = tcx.hir.krate();
    let mut items = krate.module.item_ids.clone();
    let mut path_it = path.iter().peekable();

    loop {
        let segment = match path_it.next() {
            Some(segment) => segment,
            None => return None,
        };

        for item_id in mem::replace(&mut items, hir::HirVec::new()).iter() {
            let item = tcx.hir.expect_item(item_id.id);
            if item.name == *segment {
                if path_it.peek().is_none() {
                    return Some(tcx.hir.local_def_id(item_id.id))
                }

                items = match &item.node {
                    &hir::ItemMod(ref m) => m.item_ids.clone(),
                    _ => panic!("Unexpected item {:?} in path {:?} path")
                };
                break;
            }
        }
    }
}

fn path_to_def(tcx: &TyCtxt, path: &[&str]) -> Option<DefId> {
    let crates = tcx.crates();

    let krate = crates
        .iter()
        .find(|&&krate| tcx.crate_name(krate) == path[0]);

    if let Some(krate) = krate {
        let krate = DefId {
            krate: *krate,
            index: CRATE_DEF_INDEX,
        };
        let mut items = tcx.item_children(krate);
        let mut path_it = path.iter().skip(1).peekable();

        loop {
            let segment = match path_it.next() {
                Some(segment) => segment,
                None => return None,
            };

            for item in mem::replace(&mut items, Lrc::new(vec![])).iter() {
                if item.ident.name == *segment {
                    if path_it.peek().is_none() {
                        return match item.def {
                            def::Def::Trait(did) => Some(did),
                            _ => None,
                        }
                    }

                    items = tcx.item_children(item.def.def_id());
                    break;
                }
            }
        }
    } else {
        None
    }
}
