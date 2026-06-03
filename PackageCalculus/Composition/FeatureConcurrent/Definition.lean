import PackageCalculus.Composition.FeatureConcurrent.Types
import PackageCalculus.Extensions.Feature.Definition
import PackageCalculus.Extensions.Concurrent.Definition

/-! # Feature-concurrent composition: definitions

`IsConcurrentFeatureResolution` combines the per-package feature support with
concurrent version handling: a single shared intermediate per `(parent, name)`
plus per-feature secondary intermediates, all linked via π. -/

namespace PackageCalculus.Composition

open Classical

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {F : Type*} [DecidableEq F] {G : Type*} [DecidableEq G]
variable {N_FC : Type*} [DecidableEq N_FC] {V_FC : Type*} [DecidableEq V_FC]
variable [hcnm : Concurrent.HasConcurrentNames (Feature.FeatureName N F) V G N_FC]
variable [hcvr : Concurrent.HasConcurrentVersions V G V_FC]
variable [hcfi : HasConcurrentFeatureIntermediate N V F G N_FC]

set_option linter.unusedSectionVars false

/-! ### Target resolution predicate -/

structure IsConcurrentFeatureResolution
    (R : Real N V)
    (support : Feature.Support N V F)
    (Δ_f : Feature.FeatDepRel N V F) (Δ_a : Feature.AddlDepRel N V F)
    (g : V → G) (r : Package N V)
    (S : Finset (Package N V × Finset F))
    (π : Finset (Package N V × Package N V)) : Prop where
  no_root_support : ∀ f, (r, f) ∉ support
  subset : ∀ p fs, (p, fs) ∈ S → p ∈ R
  root_mem : (r, ∅) ∈ S
  feature_unification : ∀ n v fs fs',
    ((n, v), fs) ∈ S → ((n, v), fs') ∈ S → fs = fs'
  parent_closure : ∀ p fs_p, (p, fs_p) ∈ S →
    ∀ n vs fs, (p, n, vs, fs) ∈ Δ_f →
    ∃! v, v ∈ vs ∧ (∃ fs', fs ⊆ fs' ∧ ((n, v), fs') ∈ S) ∧ ((n, v), p) ∈ π
  parent_closure_addl : ∀ p fs_p, (p, fs_p) ∈ S →
    ∀ f ∈ fs_p, ∀ n vs fs, ((p, f), n, vs, fs) ∈ Δ_a →
    ∃! v, v ∈ vs ∧ (∃ fs', fs ⊆ fs' ∧ ((n, v), fs') ∈ S) ∧ ((n, v), p) ∈ π
  π_functional : ∀ n v v' p,
    ((n, v), p) ∈ π → ((n, v'), p) ∈ π → v = v'
  version_granularity : ∀ n v v' fs fs',
    ((n, v), fs) ∈ S → ((n, v'), fs') ∈ S → v ≠ v' → g v ≠ g v'
  support_mem : ∀ n v fs f, ((n, v), fs) ∈ S → f ∈ fs → ((n, v), f) ∈ support

end PackageCalculus.Composition
