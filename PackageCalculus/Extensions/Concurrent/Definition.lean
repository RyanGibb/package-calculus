import PackageCalculus.Core.Definition
import Mathlib.Logic.Embedding.Basic

/-! # Concurrent extension: definitions

`IsConcurrentResolution` allows multiple versions per name as long as they
disagree only on a *granularity* labelling supplied by `g : V → G`. -/

namespace PackageCalculus.Concurrent

open Function

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {G : Type*}

structure IsConcurrentResolution
    (R : Real N V) (Δ : DepRel N V)
    (g : V → G) (r : Package N V)
    (S : Finset (Package N V)) (π : Finset (Package N V × Package N V)) : Prop where
  subset : S ⊆ R
  root_mem : r ∈ S
  /-- Each dependency is satisfied by exactly one compatible version, witnessed by π. -/
  parent_closure : ∀ p ∈ S, ∀ m : N, ∀ vs : Finset V,
    (p, m, vs) ∈ Δ → ∃! v, v ∈ vs ∧ (m, v) ∈ S ∧ ((m, v), p) ∈ π
  /-- Same name, different version implies different granularity. -/
  version_granularity : ∀ n : N, ∀ v v' : V,
    (n, v) ∈ S → (n, v') ∈ S → v ≠ v' → g v ≠ g v'
  /-- π ⊆ S × S: both ends of every parent edge are in the resolution. -/
  parent_subset : ∀ c p : Package N V, (c, p) ∈ π → c ∈ S ∧ p ∈ S

/-- No `orig` embedding: names are either `granular n g` or `intermediate n v m`. -/
class HasConcurrentNames (N V G : Type*) (N' : outParam Type*) where
  granularN : N → G → N'
  granularN_injective : Injective2 granularN
  intermediateN : N → V → N → N'
  intermediateN_injective : ∀ n₁ v₁ m₁ n₂ v₂ m₂,
    intermediateN n₁ v₁ m₁ = intermediateN n₂ v₂ m₂ → n₁ = n₂ ∧ v₁ = v₂ ∧ m₁ = m₂
  granularN_ne_intermediateN : ∀ n g n' v m, granularN n g ≠ intermediateN n' v m
  intermediateN_ne_granularN : ∀ n v m n' g, intermediateN n v m ≠ granularN n' g
  /-- Decidable partial inverse of `granularN`. -/
  tryGranularN : N' → Option (N × G)
  tryGranularN_granularN : ∀ n g, tryGranularN (granularN n g) = some (n, g)
  tryGranularN_some : ∀ n' p, tryGranularN n' = some p → granularN p.1 p.2 = n'

attribute [simp] HasConcurrentNames.granularN_ne_intermediateN
  HasConcurrentNames.intermediateN_ne_granularN

class HasConcurrentVersions (V G : Type*) (V' : outParam Type*) where
  origV : V ↪ V'
  granV : G ↪ V'
  origV_ne_granV : ∀ v g, origV v ≠ granV g
  granV_ne_origV : ∀ g v, granV g ≠ origV v
  /-- Decidable partial inverse of `origV`. -/
  tryOrigV : V' → Option V
  tryOrigV_origV : ∀ v, tryOrigV (origV v) = some v
  tryOrigV_some : ∀ v' v, tryOrigV v' = some v → origV v = v'

attribute [simp] HasConcurrentVersions.origV_ne_granV HasConcurrentVersions.granV_ne_origV

end PackageCalculus.Concurrent
