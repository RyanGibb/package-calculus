import PackageCalculus.Core.Definition
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Finset.Image

/-! # Conflict extension: definitions

A `ConflictRel` records pairs `(p, n, vs)` where package `p` excludes name `n`
at versions `vs`. `IsConflictResolution` extends `IsResolution` with the
constraint that no excluded package may be present. -/

namespace PackageCalculus.Conflict

open Function

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]

/-- p Γ (n, vs) means package p conflicts with name n at versions vs. -/
abbrev ConflictRel (N V : Type*) := Finset (Package N V × N × Finset V)

structure IsConflictResolution (R : Real N V) (Δ : DepRel N V)
    (Γ : ConflictRel N V) (r : Package N V) (S : Finset (Package N V)) : Prop where
  core : IsResolution R Δ r S
  conflict_avoidance : ∀ p ∈ S, ∀ n : N, ∀ vs : Finset V,
    (p, n, vs) ∈ Γ → ¬∃ v ∈ vs, (n, v) ∈ S

/-! ## Extended type interfaces

Each reduction encodes extension-specific constraints by extending the name and
version types with synthetic constructors. These typeclasses abstract over the
extended types so that lifting functions (`liftReal`, `liftDeps`, etc.) only see
their own constructors and are agnostic to constructors added by other
extensions. This makes lifting modular under reduction composition: composing
multiple reductions produces a type with constructors from all of them, but each
extension's lift still works unchanged.

Crucially, this allows lifting a single extension out of a composed type without
unwrapping the others. A solver producing a core resolution over the
fully-composed type can be lifted directly by any extension whose constraints
the consumer cares about, ignoring unsupported extensions entirely. -/

class HasConflictNames (N V : Type*) (N' : outParam Type*) where
  origN : N ↪ N'
  /-- Synthetic conflict-witness name for a (name, version-set) pair. -/
  syntheticN : N → Finset V → N'
  syntheticN_injective : Injective2 syntheticN
  origN_ne_syntheticN : ∀ n₁ n₂ (vs : Finset V), origN n₁ ≠ syntheticN n₂ vs
  syntheticN_ne_origN : ∀ n₁ (vs : Finset V) n₂, syntheticN n₁ vs ≠ origN n₂
  /-- Decidable partial inverse of `origN`. -/
  tryOrigN : N' → Option N
  tryOrigN_origN : ∀ n, tryOrigN (origN n) = some n
  tryOrigN_some : ∀ n' n, tryOrigN n' = some n → origN n = n'
  /-- Decidable partial inverse of `syntheticN`. -/
  trySyntheticN : N' → Option (N × Finset V)
  trySyntheticN_syntheticN : ∀ n vs, trySyntheticN (syntheticN n vs) = some (n, vs)
  trySyntheticN_some : ∀ n' p, trySyntheticN n' = some p → syntheticN p.1 p.2 = n'

attribute [simp] HasConflictNames.origN_ne_syntheticN HasConflictNames.syntheticN_ne_origN

class HasConflictVersions (V : Type*) (V' : outParam Type*) where
  origV : V ↪ V'
  /-- Synthetic zero version for conflict witnesses. -/
  zeroV : V'
  /-- Synthetic one version for conflict witnesses. -/
  oneV : V'
  origV_ne_zeroV : ∀ v, origV v ≠ zeroV
  zeroV_ne_origV : ∀ v, zeroV ≠ origV v
  origV_ne_oneV : ∀ v, origV v ≠ oneV
  oneV_ne_origV : ∀ v, oneV ≠ origV v
  zeroV_ne_oneV : zeroV ≠ oneV
  oneV_ne_zeroV : oneV ≠ zeroV
  /-- Decidable partial inverse of `origV`. -/
  tryOrigV : V' → Option V
  tryOrigV_origV : ∀ v, tryOrigV (origV v) = some v
  tryOrigV_some : ∀ v' v, tryOrigV v' = some v → origV v = v'

attribute [simp] HasConflictVersions.origV_ne_zeroV HasConflictVersions.zeroV_ne_origV
  HasConflictVersions.origV_ne_oneV HasConflictVersions.oneV_ne_origV
  HasConflictVersions.zeroV_ne_oneV HasConflictVersions.oneV_ne_zeroV

end PackageCalculus.Conflict
