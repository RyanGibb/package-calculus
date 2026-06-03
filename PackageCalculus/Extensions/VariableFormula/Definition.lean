import PackageCalculus.Extensions.PackageFormula.Definition
import PackageCalculus.Extensions.Conflict.Definition
import PackageCalculus.Versions.Formula
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Finset.Image

/-! # Variable-formula extension: definitions

Formulae that quantify over package variables and version variables, including
comparison predicates `x ω y`. Defines `IsVFResolution` and the
companion notion of a satisfying assignment. -/

namespace PackageCalculus.VarFormula

open Function PackageCalculus

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {X : Type*} [DecidableEq X] {Y : Type*} [DecidableEq Y]

/-- Boolean formula over package dependencies and variable comparisons.

This mirrors `PkgFormula.Formula` with one additional production for variable
comparisons: `x ω y`. There is a single variable space `X` of variable names
and a single value space `Y`; package-local variables are obtained by
user-level namespacing of names in `X`. -/
inductive Formula (N V X Y : Type*) where
  | dep : N → Finset V → Formula N V X Y
  | conj : Formula N V X Y → Formula N V X Y → Formula N V X Y
  | disj : Formula N V X Y → Formula N V X Y → Formula N V X Y
  | neg : Formula N V X Y → Formula N V X Y
  | varCmp : X → CmpOp → Y → Formula N V X Y
  deriving DecidableEq

/-- Variable-formula dependency relation: (package, variable-formula). -/
abbrev VFDepRel (N V : Type*) [DecidableEq N] [DecidableEq V]
    (X Y : Type*) [DecidableEq X] [DecidableEq Y] :=
  Finset (Package N V × Formula N V X Y)

/-- Satisfaction relation `(S, σ) ⊨ ψ`. No depender context: variable
comparisons are evaluated using the global assignment `σ : X → Y`. -/
def Formula.satisfies [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S : Finset (Package N V)) (σ : X → Y) : Formula N V X Y → Prop
  | .dep n vs => ∃ v ∈ vs, (n, v) ∈ S
  | .conj ψ₁ ψ₂ => ψ₁.satisfies S σ ∧ ψ₂.satisfies S σ
  | .disj ψ₁ ψ₂ => ψ₁.satisfies S σ ∨ ψ₂.satisfies S σ
  | .neg ψ => ¬ψ.satisfies S σ
  | .varCmp x ω y => ω.eval (σ x) y

/-- Satisfaction is decidable: a finite Boolean combination of bounded
existentials over finite sets and decidable comparison evaluations. -/
instance Formula.decidableSatisfies [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S : Finset (Package N V)) (σ : X → Y) :
    ∀ ψ : Formula N V X Y, Decidable (Formula.satisfies S σ ψ)
  | .dep n vs => inferInstanceAs (Decidable (∃ v ∈ vs, (n, v) ∈ S))
  | .conj ψ₁ ψ₂ =>
    haveI := Formula.decidableSatisfies S σ ψ₁
    haveI := Formula.decidableSatisfies S σ ψ₂
    inferInstanceAs (Decidable (Formula.satisfies S σ ψ₁ ∧ Formula.satisfies S σ ψ₂))
  | .disj ψ₁ ψ₂ =>
    haveI := Formula.decidableSatisfies S σ ψ₁
    haveI := Formula.decidableSatisfies S σ ψ₂
    inferInstanceAs (Decidable (Formula.satisfies S σ ψ₁ ∨ Formula.satisfies S σ ψ₂))
  | .neg ψ =>
    haveI := Formula.decidableSatisfies S σ ψ
    inferInstanceAs (Decidable ¬ Formula.satisfies S σ ψ)
  | .varCmp x ω y => inferInstanceAs (Decidable (ω.eval (σ x) y = true))

structure IsVFResolution [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (R : Real N V) (Δ_Ψ : VFDepRel N V X Y)
    (r : Package N V) (S : Finset (Package N V))
    (σ : X → Y) : Prop where
  subset : S ⊆ R
  root_mem : r ∈ S
  formula_closure : ∀ p ∈ S, ∀ ψ : Formula N V X Y,
    (p, ψ) ∈ Δ_Ψ → ψ.satisfies S σ
  version_unique : VersionUnique S

/-- Names structure for the Variable Formula extension. Single variable name
embedding `varN : X → N'` (no global/local split). Disjunction witness names
are per-formula, mirroring PF. -/
class HasVFNames (N V X Y : Type*) (N' : outParam Type*)
    extends Conflict.HasConflictNames N V N' where
  /-- Synthetic name for a variable `x ∈ X`. -/
  varN : X ↪ N'
  /-- Synthetic name for a disjunction witness (per-formula, inherited from PF). -/
  disjunctN : Formula N V X Y → Formula N V X Y → N'
  disjunctN_injective : Injective2 disjunctN
  origN_ne_varN : ∀ n x, origN n ≠ varN x
  varN_ne_origN : ∀ x n, varN x ≠ origN n
  origN_ne_disjunctN : ∀ n (ψ₁ ψ₂ : Formula N V X Y), origN n ≠ disjunctN ψ₁ ψ₂
  disjunctN_ne_origN : ∀ (ψ₁ ψ₂ : Formula N V X Y) n, disjunctN ψ₁ ψ₂ ≠ origN n
  varN_ne_disjunctN : ∀ x (ψ₁ ψ₂ : Formula N V X Y), varN x ≠ disjunctN ψ₁ ψ₂
  disjunctN_ne_varN : ∀ (ψ₁ ψ₂ : Formula N V X Y) x, disjunctN ψ₁ ψ₂ ≠ varN x
  varN_ne_syntheticN : ∀ x m vs, varN x ≠ syntheticN m vs
  syntheticN_ne_varN : ∀ m vs x, syntheticN m vs ≠ varN x
  disjunctN_ne_syntheticN : ∀ (ψ₁ ψ₂ : Formula N V X Y) m vs,
    disjunctN ψ₁ ψ₂ ≠ syntheticN m vs
  syntheticN_ne_disjunctN : ∀ m vs (ψ₁ ψ₂ : Formula N V X Y),
    syntheticN m vs ≠ disjunctN ψ₁ ψ₂

attribute [simp]
  HasVFNames.origN_ne_varN HasVFNames.varN_ne_origN
  HasVFNames.origN_ne_disjunctN HasVFNames.disjunctN_ne_origN
  HasVFNames.varN_ne_disjunctN HasVFNames.disjunctN_ne_varN
  HasVFNames.varN_ne_syntheticN HasVFNames.syntheticN_ne_varN
  HasVFNames.disjunctN_ne_syntheticN HasVFNames.syntheticN_ne_disjunctN

/-- Versions structure: embeds variable values `Y` into the core version
type `V'`. -/
class HasVFVersions (V Y : Type*) (V' : outParam Type*)
    extends Conflict.HasConflictVersions V V' where
  /-- Embed a variable value into the core version space. -/
  varValV : Y ↪ V'
  origV_ne_varValV : ∀ v y, origV v ≠ varValV y
  varValV_ne_origV : ∀ y v, varValV y ≠ origV v
  zeroV_ne_varValV : ∀ y, zeroV ≠ varValV y
  varValV_ne_zeroV : ∀ y, varValV y ≠ zeroV
  oneV_ne_varValV : ∀ y, oneV ≠ varValV y
  varValV_ne_oneV : ∀ y, varValV y ≠ oneV

attribute [simp]
  HasVFVersions.origV_ne_varValV HasVFVersions.varValV_ne_origV
  HasVFVersions.zeroV_ne_varValV HasVFVersions.varValV_ne_zeroV
  HasVFVersions.oneV_ne_varValV HasVFVersions.varValV_ne_oneV

end PackageCalculus.VarFormula
