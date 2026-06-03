import PackageCalculus.Core.Definition
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Finset.Image

/-! # Feature extension: definitions

Per-package feature flags drawn from `F`, together with feature-level
dependency (`FeatDepRel`) and additional-dependency (`AddlDepRel`) relations
and the `IsFeatureResolution` structure. -/

namespace PackageCalculus.Feature

open Function

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {F : Type*} [DecidableEq F]

/-- (p, f) in support means package p supports feature f. -/
abbrev Support (N V : Type*) [DecidableEq N] [DecidableEq V] (F : Type*) [DecidableEq F] :=
  Finset (Package N V × F)

/-- Feature dependency relation: (package, name, versions, required-features). -/
abbrev FeatDepRel (N V : Type*) [DecidableEq N] [DecidableEq V] (F : Type*) [DecidableEq F] :=
  Finset (Package N V × N × Finset V × Finset F)

/-- Additional dependency relation: ((package, feature), name, versions, required-features). -/
abbrev AddlDepRel (N V : Type*) [DecidableEq N] [DecidableEq V] (F : Type*) [DecidableEq F] :=
  Finset ((Package N V × F) × N × Finset V × Finset F)

structure IsFeatureResolution
    (R : Real N V)
    (support : Support N V F)
    (Δ_f : FeatDepRel N V F) (Δ_a : AddlDepRel N V F)
    (r : Package N V)
    (S : Finset (Package N V × Finset F)) : Prop where
  no_root_support : ∀ f, (r, f) ∉ support
  subset : ∀ p fs, (p, fs) ∈ S → p ∈ R
  root_mem : (r, ∅) ∈ S
  feat_dep_closure : ∀ p fs_p, (p, fs_p) ∈ S →
    ∀ n vs fs, (p, n, vs, fs) ∈ Δ_f →
    ∃ v ∈ vs, ∃ fs', fs ⊆ fs' ∧ ((n, v), fs') ∈ S
  addl_dep_closure : ∀ p fs_p, (p, fs_p) ∈ S →
    ∀ f ∈ fs_p, ∀ n vs fs, ((p, f), n, vs, fs) ∈ Δ_a →
    ∃ v ∈ vs, ∃ fs', fs ⊆ fs' ∧ ((n, v), fs') ∈ S
  feature_unification : ∀ n v v' fs fs',
    ((n, v), fs) ∈ S → ((n, v'), fs') ∈ S → fs = fs'
  version_unique : ∀ n v v' fs fs',
    ((n, v), fs) ∈ S → ((n, v'), fs') ∈ S → v = v'
  support_mem : ∀ n v fs f, ((n, v), fs) ∈ S → f ∈ fs → ((n, v), f) ∈ support

class HasFeatureNames (N F : Type*) (N' : outParam Type*) where
  origN : N ↪ N'
  /-- Synthetic name for a (name, feature) pair. -/
  featuredN : N → F → N'
  featuredN_injective : Injective2 featuredN
  origN_ne_featuredN : ∀ n₁ n₂ f, origN n₁ ≠ featuredN n₂ f
  featuredN_ne_origN : ∀ n₁ f n₂, featuredN n₁ f ≠ origN n₂
  /-- Decidable partial inverse of `origN`. -/
  tryOrigN : N' → Option N
  tryOrigN_origN : ∀ n, tryOrigN (origN n) = some n
  tryOrigN_some : ∀ n' n, tryOrigN n' = some n → origN n = n'

attribute [simp] HasFeatureNames.origN_ne_featuredN HasFeatureNames.featuredN_ne_origN

end PackageCalculus.Feature
