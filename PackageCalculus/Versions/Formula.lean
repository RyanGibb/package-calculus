import PackageCalculus.Core.Definition
import Mathlib.Data.Finset.Image

namespace PackageCalculus

variable (V : Type*)

inductive CmpOp where | ge | gt | le | lt | eq | ne deriving DecidableEq

inductive VersionFormula (V : Type*) where
  | top : VersionFormula V
  | conj : VersionFormula V → VersionFormula V → VersionFormula V
  | disj : VersionFormula V → VersionFormula V → VersionFormula V
  | cmp : CmpOp → V → VersionFormula V
  deriving DecidableEq

variable {V : Type*} [DecidableEq V] {N : Type*} [DecidableEq N]

def CmpOp.eval [LT V] [DecidableRel (· < · : V → V → Prop)]
    (ω : CmpOp) (v c : V) : Bool :=
  match ω with
  | .ge => !decide (v < c)
  | .gt => decide (c < v)
  | .le => !decide (c < v)
  | .lt => decide (v < c)
  | .eq => decide (v = c)
  | .ne => !decide (v = c)

/-- The versions in `Vn` that satisfy `φ`. -/
def VersionFormula.eval [LT V] [DecidableRel (· < · : V → V → Prop)]
    (φ : VersionFormula V) (Vn : Finset V) : Finset V :=
  match φ with
  | .top => Vn
  | .conj φ₁ φ₂ => φ₁.eval Vn ∩ φ₂.eval Vn
  | .disj φ₁ φ₂ => φ₁.eval Vn ∪ φ₂.eval Vn
  | .cmp ω c => Vn.filter (fun v => ω.eval v c)

abbrev VFDepRel (N V : Type*) [DecidableEq N] [DecidableEq V] :=
  Finset (Package N V × N × VersionFormula V)

/-- The versions of name `m` available in `R`. -/
def repoVersions (R : Real N V) (m : N) : Finset V :=
  (R.filter (fun p => p.1 = m)).image Prod.snd

/-- Like IsResolution but dependency closure uses formula semantics. -/
structure IsVFResolution [LT V] [DecidableRel (· < · : V → V → Prop)]
    (R : Real N V)
    (Δ_Φ : VFDepRel N V)
    (r : Package N V)
    (S : Finset (Package N V)) : Prop where
  subset : S ⊆ R
  root_mem : r ∈ S
  dep_closure : ∀ p ∈ S, ∀ m : N, ∀ φ : VersionFormula V,
    (p, m, φ) ∈ Δ_Φ → ∃ v ∈ φ.eval (repoVersions R m), (m, v) ∈ S
  version_unique : VersionUnique S

end PackageCalculus
