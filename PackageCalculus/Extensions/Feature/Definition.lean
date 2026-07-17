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

/-- **Groundedness of a support relation.** Every supported package is real.
The reduction only materialises feature packages (and their base back-edges)
for real packages, so support facts over non-repository packages leave no
trace in the reduced problem; this is the condition under which the support
relation is recoverable (transpiling retraction). -/
def Support.GroundedIn (support : Support N V F) (R : Real N V) : Prop :=
  ∀ p f, (p, f) ∈ support → p ∈ R

/-- The standing Functional-in-Name normalisation (Def 3.1.2), extended to
feature dependencies: a package depends on a given name with at most one
version set and required-feature set. -/
def FeatDepRel.FunctionalInName (Δ_f : FeatDepRel N V F) : Prop :=
  ∀ p n vs₁ fs₁ vs₂ fs₂,
    (p, n, vs₁, fs₁) ∈ Δ_f → (p, n, vs₂, fs₂) ∈ Δ_f → vs₁ = vs₂ ∧ fs₁ = fs₂

/-- The standing Functional-in-Name normalisation (Def 3.1.2), extended to
additional dependencies: a (package, feature) pair depends on a given name
with at most one version set and required-feature set. -/
def AddlDepRel.FunctionalInName (Δ_a : AddlDepRel N V F) : Prop :=
  ∀ pf m vs₁ fs₁ vs₂ fs₂,
    (pf, m, vs₁, fs₁) ∈ Δ_a → (pf, m, vs₂, fs₂) ∈ Δ_a → vs₁ = vs₂ ∧ fs₁ = fs₂

/-- **Base-requirement irredundancy.** No additional dependency restates the
automatic base requirement `⟨⟨n,v⟩,f⟩ → n ∋ {v}` that feature activation
already enforces for a supported real package. The reduction emits exactly
this edge for every grounded support fact, so a redundant `Δ_a` entry of this
shape is indistinguishable from it in the reduced problem; irredundancy is the
condition under which the additional-dependency relation is recoverable on the
nose (without it, recovery is exact up to the
base-requirement closure). -/
def AddlDepRel.BaseIrredundant (Δ_a : AddlDepRel N V F) (R : Real N V)
    (support : Support N V F) : Prop :=
  ∀ n v f, ((n, v), f) ∈ support → (n, v) ∈ R → (((n, v), f), n, {v}, ∅) ∉ Δ_a

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
  /-- Decidable partial inverse of `featuredN`. -/
  tryFeaturedN : N' → Option (N × F)
  tryFeaturedN_featuredN : ∀ n f, tryFeaturedN (featuredN n f) = some (n, f)
  tryFeaturedN_some : ∀ n' p, tryFeaturedN n' = some p → featuredN p.1 p.2 = n'

attribute [simp] HasFeatureNames.origN_ne_featuredN HasFeatureNames.featuredN_ne_origN

end PackageCalculus.Feature
