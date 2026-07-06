import PackageCalculus.Core.Definition
import PackageCalculus.Extensions.Conflict.Definition
import Mathlib.Logic.Embedding.Basic

/-! # Package-formula extension: definitions

Boolean formulae over package-version dependencies, satisfaction by a
resolution, and the `IsPFResolution` structure. -/

namespace PackageCalculus.PkgFormula

open Function

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]

/-- Boolean formula over package dependencies. -/
inductive Formula (N V : Type*) where
  | dep : N → Finset V → Formula N V
  | conj : Formula N V → Formula N V → Formula N V
  | disj : Formula N V → Formula N V → Formula N V
  | neg : Formula N V → Formula N V
  deriving DecidableEq

def Formula.satisfies (S : Finset (Package N V)) : Formula N V → Prop
  | .dep n vs => ∃ v ∈ vs, (n, v) ∈ S
  | .conj ψ₁ ψ₂ => ψ₁.satisfies S ∧ ψ₂.satisfies S
  | .disj ψ₁ ψ₂ => ψ₁.satisfies S ∨ ψ₂.satisfies S
  | .neg ψ => ¬ψ.satisfies S

/-- Notation: `S ⊨ ψ` means the resolution set `S` satisfies formula `ψ`. -/
notation:50 S " ⊨ " ψ => Formula.satisfies S ψ

/-- Satisfaction is decidable: the formula is a finite Boolean combination of
bounded existentials over finite sets. -/
instance Formula.decidableSatisfies (S : Finset (Package N V)) :
    ∀ ψ : Formula N V, Decidable (Formula.satisfies S ψ)
  | .dep n vs => inferInstanceAs (Decidable (∃ v ∈ vs, (n, v) ∈ S))
  | .conj ψ₁ ψ₂ =>
    haveI := Formula.decidableSatisfies S ψ₁
    haveI := Formula.decidableSatisfies S ψ₂
    inferInstanceAs (Decidable (Formula.satisfies S ψ₁ ∧ Formula.satisfies S ψ₂))
  | .disj ψ₁ ψ₂ =>
    haveI := Formula.decidableSatisfies S ψ₁
    haveI := Formula.decidableSatisfies S ψ₂
    inferInstanceAs (Decidable (Formula.satisfies S ψ₁ ∨ Formula.satisfies S ψ₂))
  | .neg ψ =>
    haveI := Formula.decidableSatisfies S ψ
    inferInstanceAs (Decidable ¬ Formula.satisfies S ψ)

/-- Package-formula dependency relation: (package, formula). -/
abbrev PFDepRel (N V : Type*) [DecidableEq N] [DecidableEq V] :=
  Finset (Package N V × Formula N V)

structure IsPFResolution (R : Real N V) (Δ_Ψ : PFDepRel N V)
    (r : Package N V) (S : Finset (Package N V)) : Prop where
  subset : S ⊆ R
  root_mem : r ∈ S
  formula_closure : ∀ p ∈ S, ∀ ψ : Formula N V,
    (p, ψ) ∈ Δ_Ψ → S ⊨ ψ
  version_unique : VersionUnique S

class HasPFNames (N V : Type*) (N' : outParam Type*) extends Conflict.HasConflictNames N V N' where
  /-- Synthetic name for a disjunction witness. -/
  disjunctN : Formula N V → Formula N V → N'
  disjunctN_injective : Injective2 disjunctN
  origN_ne_disjunctN : ∀ n ψ₁ ψ₂, origN n ≠ disjunctN ψ₁ ψ₂
  disjunctN_ne_origN : ∀ ψ₁ ψ₂ n, disjunctN ψ₁ ψ₂ ≠ origN n
  disjunctN_ne_syntheticN : ∀ ψ₁ ψ₂ m vs, disjunctN ψ₁ ψ₂ ≠ syntheticN m vs
  syntheticN_ne_disjunctN : ∀ m vs ψ₁ ψ₂, syntheticN m vs ≠ disjunctN ψ₁ ψ₂
  /-- Decidable partial inverse of `disjunctN`. -/
  tryDisjunctN : N' → Option (Formula N V × Formula N V)
  tryDisjunctN_disjunctN : ∀ ψ₁ ψ₂, tryDisjunctN (disjunctN ψ₁ ψ₂) = some (ψ₁, ψ₂)
  tryDisjunctN_some : ∀ n' q, tryDisjunctN n' = some q → disjunctN q.1 q.2 = n'

attribute [simp] HasPFNames.origN_ne_disjunctN HasPFNames.disjunctN_ne_origN
  HasPFNames.disjunctN_ne_syntheticN HasPFNames.syntheticN_ne_disjunctN

end PackageCalculus.PkgFormula
