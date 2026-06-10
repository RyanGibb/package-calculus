import Mathlib.Data.Set.Basic

/-! # 3SAT primitives

Literals, three-literal clauses, and satisfaction by a Boolean assignment.
Used as the source instance for the NP-hardness reduction. -/

namespace PackageCalculus.Complexity

variable {Var : Type*}

/-- A propositional literal: a variable with polarity. -/
structure Literal (Var : Type*) where
  var : Var
  /-- True for positive, false for negated. -/
  pos : Bool
  deriving DecidableEq

structure ThreeClause (Var : Type*) where
  l₁ : Literal Var
  l₂ : Literal Var
  l₃ : Literal Var

def Literal.eval (σ : Var → Bool) (l : Literal Var) : Bool :=
  if l.pos then σ l.var else !σ l.var

theorem Literal.eval_true_iff {σ : Var → Bool} {l : Literal Var} :
    l.eval σ = true ↔ σ l.var = l.pos := by
  unfold Literal.eval; cases l.pos <;> simp

def ThreeClause.satisfiedBy (σ : Var → Bool) (c : ThreeClause Var) : Prop :=
  c.l₁.eval σ = true ∨ c.l₂.eval σ = true ∨ c.l₃.eval σ = true

end PackageCalculus.Complexity
