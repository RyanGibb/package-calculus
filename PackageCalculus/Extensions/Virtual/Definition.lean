import PackageCalculus.Core.Definition
import Mathlib.Logic.Embedding.Basic

/-! # Virtual extension: definitions

Virtual packages selecting concrete providers, encoded through a `provides`
relation and the `IsVirtualResolution` structure. -/

namespace PackageCalculus.Virtual

open Function

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]

/-- A version or top (wildcard). -/
inductive VTop (V : Type*) where
  | val : V → VTop V
  | top : VTop V
  deriving DecidableEq

/-- Provides relation: (provider-package, virtual-name, version-or-top). -/
abbrev ProvidesRel (N V : Type*) [DecidableEq N] [DecidableEq V] :=
  Finset (Package N V × N × VTop V)

/-- v matches vs; top matches anything. -/
def memTop (v : VTop V) (vs : Finset V) : Prop :=
  match v with
  | .top => True
  | .val v' => v' ∈ vs

structure IsVirtualResolution
    (R : Real N V) (Delta : DepRel N V)
    (prov : ProvidesRel N V) (r : Package N V)
    (S : Finset (Package N V))
    (rho : Finset (Package N V × N × Package N V)) : Prop where
  subset : S ⊆ R
  root_mem : r ∈ S
  /-- Either a direct version is selected, or exactly one provider satisfies the dep via rho. -/
  virtual_dep_closure : ∀ p ∈ S, ∀ n : N, ∀ vs : Finset V,
    (p, n, vs) ∈ Delta →
    (∃ v ∈ vs, (n, v) ∈ S) ∨
    (∃! q, q ∈ S ∧ ∃ v, memTop v vs ∧ (q, n, v) ∈ prov ∧ (q, n, p) ∈ rho)
  version_unique : VersionUnique S
  /-- rho ⊆ S × N × S: every provider edge relates members of the resolution. -/
  provider_subset : ∀ q : Package N V, ∀ n : N, ∀ p : Package N V,
    (q, n, p) ∈ rho → q ∈ S ∧ p ∈ S

class HasVirtualNames (N V : Type*) (N' : outParam Type*) where
  origN : N ↪ N'
  /-- Synthetic selector name for a (package, dep-name) pair. -/
  selectorN : Package N V → N → N'
  selectorN_injective : Injective2 selectorN
  origN_ne_selectorN : ∀ n p m, origN n ≠ selectorN p m
  selectorN_ne_origN : ∀ p m n, selectorN p m ≠ origN n
  /-- Decidable partial inverse of `origN`. -/
  tryOrigN : N' → Option N
  tryOrigN_origN : ∀ n, tryOrigN (origN n) = some n
  tryOrigN_some : ∀ n' n, tryOrigN n' = some n → origN n = n'
  /-- Decidable partial inverse of `selectorN`. -/
  trySelectorN : N' → Option (Package N V × N)
  trySelectorN_selectorN : ∀ p n, trySelectorN (selectorN p n) = some (p, n)
  trySelectorN_some : ∀ n' q, trySelectorN n' = some q → selectorN q.1 q.2 = n'

attribute [simp] HasVirtualNames.origN_ne_selectorN HasVirtualNames.selectorN_ne_origN

class HasVirtualVersions (N V : Type*) (V' : outParam Type*) where
  origV : V ↪ V'
  /-- Synthetic provider version indexed by (name, version). -/
  providerV : N → V → V'
  providerV_injective : Injective2 providerV
  origV_ne_providerV : ∀ v n w, origV v ≠ providerV n w
  providerV_ne_origV : ∀ n w v, providerV n w ≠ origV v
  /-- Decidable partial inverse of `origV`. -/
  tryOrigV : V' → Option V
  tryOrigV_origV : ∀ v, tryOrigV (origV v) = some v
  tryOrigV_some : ∀ v' v, tryOrigV v' = some v → origV v = v'
  /-- Decidable partial inverse of `providerV`. -/
  tryProviderV : V' → Option (N × V)
  tryProviderV_providerV : ∀ n w, tryProviderV (providerV n w) = some (n, w)
  tryProviderV_some : ∀ v' q, tryProviderV v' = some q → providerV q.1 q.2 = v'

attribute [simp] HasVirtualVersions.origV_ne_providerV HasVirtualVersions.providerV_ne_origV

/-- **No self-provides.** No package provides its own name: provided names are
properly virtual. The reduction routes a dependency on a virtual name through
selector packages whose versions mirror the chosen provider; a self-provider
`⟨⟨n,w⟩, n, v⟩` would make its selector→provider edge structurally identical to
the selector→direct edge for the real version `w` of `n`, so the direct version
set could not be separated from the providers in the reduced problem. This is
the condition under which the dependency relation is recoverable up to
`restrictReal` (§5.2 transpiling retraction). -/
def ProvidesRel.NoSelfProvides (prov : ProvidesRel N V) : Prop :=
  ∀ q n v, (q, n, v) ∈ prov → q.1 ≠ n

end PackageCalculus.Virtual
