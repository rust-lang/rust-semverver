//! The type and predicate checking logic used to compare types of corresponding items.
//!
//! Multiple context structures are provided that modularize the needed functionality to allow
//! for code reuse across analysis steps.

use rustc::hir::def_id::DefId;
use rustc::infer::InferCtxt;
use rustc::traits::{auto_trait,
                    FulfillmentContext, FulfillmentError,
                    Obligation, ObligationCause};
use rustc::ty::{ParamEnv, Predicate, TraitRef, Ty, TyCtxt, UniverseIndex};
use rustc::ty::error::TypeError;
use rustc::ty::fold::TypeFoldable;
use rustc::ty::subst::Substs;

use rustc_data_structures::fx::FxHashSet;

use semcheck::changes::ChangeSet;
use semcheck::mapping::IdMapping;
use semcheck::translate::{InferenceCleanupFolder, TranslationContext};

pub struct AutoTraitTable {
    send_did: DefId,
    sync_did: DefId,
}

impl AutoTraitTable {
    pub fn new(tcx: &TyCtxt) -> Option<Self> {
        // TODO: use the local method if possible
        use semcheck::util::get_trait_def_id;
        let send_did =
            if let Some(did) = get_trait_def_id(tcx, &["core", "marker", "Send"], false) {
                did
            } else {
                return None;
            };

        let sync_did =
            if let Some(did) = get_trait_def_id(tcx, &["core", "marker", "Sync"], false) {
                did
            } else {
                return None;
            };

        Some(AutoTraitTable { send_did, sync_did, })
    }

    pub fn all_auto_traits(&self) -> impl Iterator<Item=(DefId, &'static str)> {
        use std::iter::once;

        once((self.send_did, "Send")).chain(once((self.sync_did, "Sync")))
    }
}

/// The context in which bounds analysis happens.
pub struct BoundContext<'a, 'gcx: 'a + 'tcx, 'tcx: 'a> {
    /// The inference context to use.
    infcx: &'a InferCtxt<'a, 'gcx, 'tcx>,
    /// The fulfillment context to use.
    fulfill_cx: FulfillmentContext<'tcx>,
    /// The param env to be assumed.
    given_param_env: ParamEnv<'tcx>,
}

impl<'a, 'gcx, 'tcx> BoundContext<'a, 'gcx, 'tcx> {
    /// Construct a new bound context.
    pub fn new(infcx: &'a InferCtxt<'a, 'gcx, 'tcx>, given_param_env: ParamEnv<'tcx>) -> Self {
        BoundContext {
            infcx: infcx,
            fulfill_cx: FulfillmentContext::new(),
            given_param_env: given_param_env,
        }
    }

    /// Register the bounds of an item.
    pub fn register(&mut self, checked_def_id: DefId, substs: &Substs<'tcx>) {
        use rustc::traits::{normalize, Normalized, SelectionContext};

        let cause = ObligationCause::dummy();
        let mut selcx = SelectionContext::new(self.infcx);
        let predicates =
            self.infcx
                .tcx
                .predicates_of(checked_def_id)
                .instantiate(self.infcx.tcx, substs);
        let Normalized { value, obligations } =
            normalize(&mut selcx, self.given_param_env, cause.clone(), &predicates);

        for obligation in obligations {
            self.fulfill_cx.register_predicate_obligation(self.infcx, obligation);
        }

        for predicate in value.predicates {
            let obligation = Obligation::new(cause.clone(), self.given_param_env, predicate);
            self.fulfill_cx.register_predicate_obligation(self.infcx, obligation);
        }
    }

    /// Register the trait bound represented by a `TraitRef`.
    pub fn register_trait_ref(&mut self, checked_trait_ref: TraitRef<'tcx>) {
        use rustc::ty::{Binder, Predicate, TraitPredicate};

        let predicate = Predicate::Trait(Binder(TraitPredicate {
            trait_ref: checked_trait_ref,
        }));
        let obligation =
            Obligation::new(ObligationCause::dummy(), self.given_param_env, predicate);
        self.fulfill_cx.register_predicate_obligation(self.infcx, obligation);
    }

    /// Return inference errors, if any.
    pub fn get_errors(&mut self) -> Option<Vec<FulfillmentError<'tcx>>> {
        if let Err(err) = self.fulfill_cx.select_all_or_error(self.infcx) {
            debug!("err: {:?}", err);
            Some(err)
        } else {
            None
        }
    }
}

/// The context in which types and their bounds can be compared.
pub struct TypeComparisonContext<'a, 'gcx: 'a + 'tcx, 'tcx: 'a> {
    /// The inference context to use.
    infcx: &'a InferCtxt<'a, 'gcx, 'tcx>,
    /// The index mapping to use.
    id_mapping: &'a IdMapping,
    /// The folder to clean up found errors of inference artifacts.
    folder: InferenceCleanupFolder<'a, 'gcx, 'tcx>,
    /// The translation context translating from original to target items.
    pub forward_trans: TranslationContext<'a, 'gcx, 'tcx>,
    /// The translation context translating from target to original items.
    pub backward_trans: TranslationContext<'a, 'gcx, 'tcx>,
    /// Whether we are checking a trait definition.
    checking_trait_def: bool,
}

impl<'a, 'gcx, 'tcx> TypeComparisonContext<'a, 'gcx, 'tcx> {
    /// Construct a new context where the original item is old.
    pub fn target_new(infcx: &'a InferCtxt<'a, 'gcx, 'tcx>,
                      id_mapping: &'a IdMapping,
                      checking_trait_def: bool) -> Self {
        let forward_trans = TranslationContext::target_new(infcx.tcx, id_mapping, false);
        let backward_trans = TranslationContext::target_old(infcx.tcx, id_mapping, false);
        TypeComparisonContext::from_trans(infcx,
                                          id_mapping,
                                          forward_trans,
                                          backward_trans,
                                          checking_trait_def)
    }

    /// Construct a new context where the original item is new.
    pub fn target_old(infcx: &'a InferCtxt<'a, 'gcx, 'tcx>,
                      id_mapping: &'a IdMapping,
                      checking_trait_def: bool) -> Self {
        let forward_trans = TranslationContext::target_old(infcx.tcx, id_mapping, false);
        let backward_trans = TranslationContext::target_new(infcx.tcx, id_mapping, false);
        TypeComparisonContext::from_trans(infcx,
                                          id_mapping,
                                          forward_trans,
                                          backward_trans,
                                          checking_trait_def)
    }

    /// Construct a new context given a pair of translation contexts.
    fn from_trans(infcx: &'a InferCtxt<'a, 'gcx, 'tcx>,
                  id_mapping: &'a IdMapping,
                  forward_trans: TranslationContext<'a, 'gcx, 'tcx>,
                  backward_trans: TranslationContext<'a, 'gcx, 'tcx>,
                  checking_trait_def: bool) -> Self {
        TypeComparisonContext {
            infcx: infcx,
            id_mapping: id_mapping,
            folder: InferenceCleanupFolder::new(infcx),
            forward_trans: forward_trans,
            backward_trans: backward_trans,
            checking_trait_def: checking_trait_def,
        }
    }

    /// Construct a set of subsitutions for an item, which replaces all region and type variables
    /// with inference variables, with the exception of `Self`.
    pub fn compute_target_infer_substs(&self, target_def_id: DefId) -> &Substs<'tcx> {
        use syntax_pos::DUMMY_SP;

        let has_self = self.infcx.tcx.generics_of(target_def_id).has_self;

        Substs::for_item(self.infcx.tcx, target_def_id, |def, _| {
            self.infcx.region_var_for_def(DUMMY_SP, def)
        }, |def, _| {
            if def.index == 0 && has_self { // `Self` is special
                self.infcx.tcx.mk_param_from_def(def)
            } else {
                self.infcx.type_var_for_def(UniverseIndex::ROOT, DUMMY_SP, def)
            }
        })
    }

    /// Construct a set of subsitutions for an item, which normalizes defaults.
    pub fn compute_target_default_substs(&self, target_def_id: DefId) -> &Substs<'tcx> {
        use rustc::ty::ReEarlyBound;

        Substs::for_item(self.infcx.tcx, target_def_id, |def, _| {
            self.infcx.tcx.mk_region(ReEarlyBound(def.to_early_bound_region_data()))
        }, |def, _| if self.id_mapping.is_non_mapped_defaulted_type_param(&def.def_id) {
            self.infcx.tcx.type_of(def.def_id)
        } else {
            self.infcx.tcx.mk_param_from_def(def)
        })
    }

    /// Check for type mismatches in a pair of items.
    pub fn check_type_error<'b, 'tcx2>(&self,
                                       lift_tcx: TyCtxt<'b, 'tcx2, 'tcx2>,
                                       target_def_id: DefId,
                                       target_param_env: ParamEnv<'tcx>,
                                       orig: Ty<'tcx>,
                                       target: Ty<'tcx>) -> Option<TypeError<'tcx2>> {
        use rustc::infer::InferOk;
        use rustc::infer::outlives::env::OutlivesEnvironment;
        use rustc::middle::region::ScopeTree;
        use rustc::ty::Lift;

        let error =
            self.infcx
                .at(&ObligationCause::dummy(), target_param_env)
                .eq(orig, target)
                .map(|InferOk { obligations: o, .. }| { assert_eq!(o, vec![]); });

        if let Err(err) = error {
            let scope_tree = ScopeTree::default();
            let mut outlives_env = OutlivesEnvironment::new(target_param_env);

            // The old code here added the bounds from the target param env by hand. However, at
            // least the explicit bounds are added when the OutlivesEnvironment is created. This
            // seems to work, but in case it stops to do so, the below code snippets should be
            // of help to implement the old behaviour.
            //
            // outlives_env.add_outlives_bounds(None, target_param_env.caller_bounds.iter()....)
            // free_regions.relate_free_regions_from_predicates(target_param_env.caller_bounds);
            //  ty::Predicate::RegionOutlives(ty::Binder(ty::OutlivesPredicate(r_a, r_b))) => {
            //      self.relate_regions(r_b, r_a);
            //  }

            self.infcx.resolve_regions_and_report_errors(target_def_id,
                                                         &scope_tree,
                                                         &outlives_env);

            let err =
                self.infcx
                    .resolve_type_vars_if_possible(&err)
                    .fold_with(&mut self.folder.clone())
                    .lift_to_tcx(lift_tcx)
                    .unwrap();

            Some(err)
        } else {
            None
        }
    }

    /// Check for trait bound mismatches in a pair of items.
    pub fn check_bounds_error<'b, 'tcx2>(&self,
                                         lift_tcx: TyCtxt<'b, 'tcx2, 'tcx2>,
                                         orig_param_env: ParamEnv<'tcx>,
                                         target_def_id: DefId,
                                         target_substs: &Substs<'tcx>)
        -> Option<Vec<Predicate<'tcx2>>>
    {
        use rustc::ty::Lift;
        debug!("check_bounds_error: orig env: {:?}, target did: {:?}, target substs: {:?}",
               orig_param_env,
               target_def_id,
               target_substs);

        let mut bound_cx = BoundContext::new(self.infcx, orig_param_env);
        bound_cx.register(target_def_id, target_substs);

        bound_cx
            .get_errors()
            .map(|errors| errors
                .iter()
                .map(|err|
                     self.infcx
                         .resolve_type_vars_if_possible(&err.obligation.predicate)
                         .fold_with(&mut self.folder.clone())
                         .lift_to_tcx(lift_tcx)
                         .unwrap())
                .collect())
    }

    /// Check the bounds on an item in both directions and register changes found.
    pub fn check_bounds_bidirectional<'b, 'tcx2>(&self,
                                                 changes: &mut ChangeSet<'tcx2>,
                                                 lift_tcx: TyCtxt<'b, 'tcx2, 'tcx2>,
                                                 orig_def_id: DefId,
                                                 target_def_id: DefId,
                                                 orig_substs: &Substs<'tcx>,
                                                 target_substs: &Substs<'tcx>) {
        use semcheck::changes::ChangeType::{BoundsLoosened, BoundsTightened};

        let tcx = self.infcx.tcx;

        let orig_param_env = self
            .forward_trans
            .translate_param_env(orig_def_id, tcx.param_env(orig_def_id));

        let orig_param_env = if let Some(env) = orig_param_env {
            env
        } else {
            return;
        };

        if let Some(errors) =
            self.check_bounds_error(lift_tcx, orig_param_env, target_def_id, target_substs)
        {
            for err in errors {
                let err_type = BoundsTightened {
                    pred: err,
                };

                changes.add_change(err_type, orig_def_id, None);
            }
        }

        let target_param_env = self
            .backward_trans
            .translate_param_env(target_def_id, tcx.param_env(target_def_id));

        let target_param_env = if let Some(env) = target_param_env {
            env
        } else {
            return;
        };

        if let Some(errors) =
            self.check_bounds_error(lift_tcx, target_param_env, orig_def_id, orig_substs)
        {
            for err in errors {
                let err_type = BoundsLoosened {
                    pred: err,
                    trait_def: self.checking_trait_def,
                };

                changes.add_change(err_type, orig_def_id, None);
            }
        }
    }
}

/// The context in which auto trait bounds are compared.
///
/// TODO: explain why we need this.
pub struct AutoTraitComparisonContext<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    id_mapping: &'a IdMapping,
    auto_trait_table: &'a AutoTraitTable,
    // folder: InferenceCleanupFolder<'a, 'tcx, 'tcx>,
    forward_trans: TranslationContext<'a, 'tcx, 'tcx>,
    backward_trans: TranslationContext<'a, 'tcx, 'tcx>,
}

impl<'a, 'tcx> AutoTraitComparisonContext<'a, 'tcx> {
    pub fn target_new(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                      id_mapping: &'a IdMapping,
                      auto_trait_tables: &'a AutoTraitTable) -> Self {
        let forward_trans = TranslationContext::target_new(tcx, id_mapping, false);
        let backward_trans = TranslationContext::target_old(tcx, id_mapping, false);

        AutoTraitComparisonContext::from_trans(tcx,
                                               id_mapping,
                                               auto_trait_tables,
                                               forward_trans,
                                               backward_trans)
    }

    pub fn target_old(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                      id_mapping: &'a IdMapping,
                      auto_trait_tables: &'a AutoTraitTable) -> Self {
        let forward_trans = TranslationContext::target_old(tcx, id_mapping, false);
        let backward_trans = TranslationContext::target_new(tcx, id_mapping, false);

        AutoTraitComparisonContext::from_trans(tcx,
                                               id_mapping,
                                               auto_trait_tables,
                                               forward_trans,
                                               backward_trans)
    }

    pub fn from_trans(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                      id_mapping: &'a IdMapping,
                      auto_trait_table: &'a AutoTraitTable,
                      forward_trans: TranslationContext<'a, 'tcx, 'tcx>,
                      backward_trans: TranslationContext<'a, 'tcx, 'tcx>) -> Self {
        AutoTraitComparisonContext {
            tcx,
            id_mapping,
            auto_trait_table,
            forward_trans,
            backward_trans,
        }
    }

    pub fn check_all_auto_trait_bounds_bidirectional(&self,
                                                     orig_def_id: DefId,
                                                     target_def_id: DefId) {
        for (trait_def_id, trait_name) in self.auto_trait_table.all_auto_traits() {
            self.check_auto_trait_bounds_bidirectional(orig_def_id, target_def_id, trait_def_id);
        }
    }

    pub fn check_auto_trait_bounds_bidirectional(&self,
                                                 orig_def_id: DefId,
                                                 target_def_id: DefId,
                                                 trait_def_id: DefId) {
        use rustc::ty::ReEarlyBound;

        let orig_substs = Substs::identity_for_item(self.tcx, target_def_id);
        let target_substs = Substs::for_item(self.tcx, target_def_id, |def, _| {
            self.tcx.mk_region(ReEarlyBound(def.to_early_bound_region_data()))
        }, |def, _| if self.id_mapping.is_non_mapped_defaulted_type_param(&def.def_id) {
            self.tcx.type_of(def.def_id)
        } else {
            self.tcx.mk_param_from_def(def)
        });

        let orig_param_env = if let Some(orig_param_env) = self
                .get_auto_trait_bounds_param_env(orig_def_id, trait_def_id)
                .and_then(|env| self.forward_trans.translate_param_env(orig_def_id, env)) {
            debug!("orig param env for {:?}, {:?}: {:?}",
                   orig_def_id, trait_def_id, orig_param_env);
            orig_param_env
        } else {
            info!("could not determine orig param env for {:?}, {:?}",
                   orig_def_id, trait_def_id);
            return;
        };

        if let Some(errors) =
            self.check_bounds_error(orig_param_env, target_def_id, target_substs)
        {
            info!("auto trait errors are present");
            for err in errors {
                info!("found an error for auto traits: {:?}", err);
            }

            // TODO: add the changes
        } else {
            info!("no auto trait errors");
        }

        let target_param_env = if let Some(target_param_env) = self
                .get_auto_trait_bounds_param_env(target_def_id, trait_def_id)
                .and_then(|env| self.backward_trans.translate_param_env(target_def_id, env)) {
            debug!("target param env for {:?}, {:?}: {:?}",
                   target_def_id, trait_def_id, target_param_env);
            target_param_env
        } else {
            info!("could not determine target param env for {:?}, {:?}",
                   target_def_id, trait_def_id);
            return;
        };

        if let Some(errors) =
            self.check_bounds_error(target_param_env, orig_def_id, orig_substs)
        {
            info!("auto trait errors are present");
            for err in errors {
                info!("found an error for auto traits: {:?}", err);
            }

            // TODO: add the changes
        } else {
            info!("no auto trait errors");
        }

    }

    pub fn check_bounds_error(&self,
                              orig_param_env: ParamEnv<'tcx>,
                              target_def_id: DefId,
                              target_substs: &Substs<'tcx>) -> Option<Vec<Predicate<'tcx>>> {
        use rustc::ty::Lift;
        debug!("check_bounds_error(2): orig env: {:?}, target did: {:?}, target substs: {:?}",
               orig_param_env,
               target_def_id,
               target_substs);

        self.tcx.infer_ctxt().enter(|infcx| {
            let mut bound_cx = BoundContext::new(&infcx, orig_param_env);
            bound_cx.register(target_def_id, target_substs);

            debug!("get_errors(): {:?}", bound_cx.get_errors());

            bound_cx
                .get_errors()
                .map(|errors| errors
                     .iter()
                     .map(|err|
                          infcx
                              .resolve_type_vars_if_possible(&err.obligation.predicate)
                              .fold_with(&mut InferenceCleanupFolder::new(&infcx))
                              .lift_to_tcx(self.tcx)
                              .unwrap())
                .collect())
        })
    }

    pub fn get_auto_trait_bounds_param_env(&self,
                                           orig_def_id: DefId,
                                           trait_def_id: DefId) -> Option<ParamEnv<'tcx>> {
        use rustc::ty::Lift;

        let orig_ty = self.tcx.type_of(orig_def_id);
        let orig_param_env = self.tcx.param_env(orig_def_id);
        let auto_trait_finder = auto_trait::AutoTraitFinder { tcx: &self.tcx };

        self.tcx.infer_ctxt().enter(|mut infcx| {
            let mut fresh_preds = FxHashSet();
            let (full_env1, user_env1) = match auto_trait_finder.evaluate_predicates(
                    &mut infcx,
                    orig_def_id,
                    trait_def_id,
                    orig_ty,
                    orig_param_env.clone(),
                    orig_param_env,
                    &mut fresh_preds,
                    false) {
                Some(e) => e,
                None => {
                    debug!("negative impl found.");
                    return None;
                },
            };

            let full_env = auto_trait_finder.evaluate_predicates(
                &mut infcx,
                orig_def_id,
                trait_def_id,
                orig_ty,
                full_env1.clone(),
                user_env1,
                &mut fresh_preds,
                true
            ).unwrap_or_else(||
                panic!("Failed to fully process: {:?} {:?} {:?}",
                       orig_ty, trait_def_id, orig_param_env)).0;

            full_env.lift_to_tcx(self.tcx) // TODO: does this work properly?
        })
    }
}
