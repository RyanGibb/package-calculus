import PackageCalculus.Core.Definition
import PackageCalculus.Complexity.ThreeSAT
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union

/-! # NP-hardness of dependency resolution

Polynomial-time reduction from 3SAT to the resolution problem: each 3SAT
instance is encoded as `(R, Δ, root)` such that a satisfying assignment
corresponds to a resolution. -/

namespace PackageCalculus.Complexity

open Classical

variable {Var : Type*} [DecidableEq Var] {Cls : Type*} [DecidableEq Cls]

/-! ## Extended types for the reduction -/

/-- Package names for the 3-SAT reduction: root, variable, or clause. -/
inductive SATRedName (Var Cls : Type*) where
  | root : SATRedName Var Cls
  | var : Var → SATRedName Var Cls
  | clause : Cls → SATRedName Var Cls
  deriving DecidableEq

/-- Package versions for the 3-SAT reduction: unit, boolean, or literal. -/
inductive SATRedVersion (Var : Type*) where
  | unit : SATRedVersion Var
  | bool : Bool → SATRedVersion Var
  | lit : Literal Var → SATRedVersion Var
  deriving DecidableEq

/-! ## Reduction construction -/

def satRedReal (φ : Cls → ThreeClause Var) (clauses : Finset Cls) :
    Real (SATRedName Var Cls) (SATRedVersion Var) :=
  {(SATRedName.root, SATRedVersion.unit)} ∪
  Finset.biUnion clauses (fun j =>
    Finset.biUnion ({(φ j).l₁, (φ j).l₂, (φ j).l₃} : Finset (Literal Var)) (fun l =>
      {(SATRedName.var l.var, SATRedVersion.bool true),
       (SATRedName.var l.var, SATRedVersion.bool false)})) ∪
  Finset.biUnion clauses (fun j =>
    {(SATRedName.clause j, SATRedVersion.lit (φ j).l₁),
     (SATRedName.clause j, SATRedVersion.lit (φ j).l₂),
     (SATRedName.clause j, SATRedVersion.lit (φ j).l₃)})

def satRedDeps (φ : Cls → ThreeClause Var) (clauses : Finset Cls) :
    DepRel (SATRedName Var Cls) (SATRedVersion Var) :=
  Finset.image (fun j =>
    ((SATRedName.root, SATRedVersion.unit), SATRedName.clause j,
      ({SATRedVersion.lit (φ j).l₁, SATRedVersion.lit (φ j).l₂,
        SATRedVersion.lit (φ j).l₃} : Finset _))) clauses ∪
  Finset.biUnion clauses (fun j =>
    Finset.image (fun l =>
      ((SATRedName.clause j, SATRedVersion.lit l), SATRedName.var l.var,
        ({SATRedVersion.bool l.pos} : Finset _)))
      ({(φ j).l₁, (φ j).l₂, (φ j).l₃} : Finset (Literal Var)))

/-! ## Soundness helpers -/

/-- Select the first satisfied literal in a clause under assignment σ. -/
def selectLiteral (σ : Var → Bool) (c : ThreeClause Var) : Literal Var :=
  if c.l₁.eval σ = true then c.l₁
  else if c.l₂.eval σ = true then c.l₂
  else c.l₃

omit [DecidableEq Cls] in
private theorem selectLiteral_mem (σ : Var → Bool) (c : ThreeClause Var) :
    selectLiteral σ c ∈ ({c.l₁, c.l₂, c.l₃} : Finset (Literal Var)) := by
  unfold selectLiteral; split_ifs <;> simp

omit [DecidableEq Var] [DecidableEq Cls] in
private theorem selectLiteral_eval {σ : Var → Bool} {c : ThreeClause Var}
    (hsat : c.satisfiedBy σ) : (selectLiteral σ c).eval σ = true := by
  unfold selectLiteral
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · exact (hsat.elim (absurd · h1) (·.elim (absurd · h2) id))

def soundnessWitness (σ : Var → Bool) (φ : Cls → ThreeClause Var)
    (clauses : Finset Cls) : Finset (Package (SATRedName Var Cls) (SATRedVersion Var)) :=
  {(SATRedName.root, SATRedVersion.unit)} ∪
  Finset.biUnion clauses (fun j =>
    Finset.image (fun l =>
      (SATRedName.var l.var, SATRedVersion.bool (σ l.var)))
      ({(φ j).l₁, (φ j).l₂, (φ j).l₃} : Finset (Literal Var))) ∪
  Finset.image (fun j =>
    (SATRedName.clause j, SATRedVersion.lit (selectLiteral σ (φ j)))) clauses

/-! ## Soundness -/

-- Paper Appendix B (3SAT reduction, soundness).
theorem satRed_soundness
    (φ : Cls → ThreeClause Var) (clauses : Finset Cls) (σ : Var → Bool)
    (hsat : ∀ j ∈ clauses, (φ j).satisfiedBy σ) :
    IsResolution (satRedReal φ clauses) (satRedDeps φ clauses)
      (SATRedName.root, SATRedVersion.unit) (soundnessWitness σ φ clauses) := by
  constructor;
  · intro p hp;
    unfold soundnessWitness satRedReal at *; simp_all +decide ;
    rcases hp with ( rfl | ⟨ a, ha, rfl | rfl | rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> simp +decide [ selectLiteral ] at *; all_goals grind;
  · exact Finset.mem_union_left _ ( Finset.mem_union_left _ ( Finset.mem_singleton_self _ ) );
  · intro p hp m vs h;
    unfold satRedDeps at h; simp_all +decide [ Finset.mem_union, Finset.mem_image ] ;
    rcases h with ( ⟨ j, hj, rfl, rfl, rfl ⟩ | ⟨ j, hj, h | h | h ⟩ ) <;> simp_all +decide [ soundnessWitness ];
    · grind +locals;
    · have := selectLiteral_eval ( hsat j hj ) ; simp_all +decide [ Literal.eval_true_iff ] ;
      exact ⟨ j, hj, Or.inl ⟨ rfl, this.symm ⟩ ⟩;
    · have := selectLiteral_eval ( hsat j hj ) ; simp_all +decide [ Literal.eval ] ;
      grind;
    · have := selectLiteral_eval ( hsat j hj ) ; simp_all +decide [ Literal.eval ] ;
      lia;
  · unfold VersionUnique soundnessWitness;
    grind

/-! ## Completeness: resolution → satisfying assignment -/

noncomputable def extractAssignment
    (S : Finset (Package (SATRedName Var Cls) (SATRedVersion Var))) (x : Var) : Bool :=
  if h : ∃ b : Bool, (SATRedName.var x, SATRedVersion.bool b) ∈ S then h.choose else false

private theorem extractAssignment_spec
    {S : Finset (Package (SATRedName Var Cls) (SATRedVersion Var))}
    {x : Var} {b : Bool}
    (hmem : (SATRedName.var x, SATRedVersion.bool b) ∈ S)
    (huniq : ∀ (n : SATRedName Var Cls) (v v' : SATRedVersion Var),
      (n, v) ∈ S → (n, v') ∈ S → v = v') :
    extractAssignment S x = b := by
  unfold extractAssignment
  have hex : ∃ b : Bool, (SATRedName.var x, SATRedVersion.bool b) ∈ S := ⟨b, hmem⟩
  rw [dif_pos hex]
  exact SATRedVersion.bool.inj (huniq _ _ _ hex.choose_spec hmem)

-- Paper Appendix B (3SAT reduction, completeness).
theorem satRed_completeness
    (φ : Cls → ThreeClause Var) (clauses : Finset Cls)
    (S : Finset (Package (SATRedName Var Cls) (SATRedVersion Var)))
    (hres : IsResolution (satRedReal φ clauses) (satRedDeps φ clauses)
      (SATRedName.root, SATRedVersion.unit) S) :
    ∀ j ∈ clauses, (φ j).satisfiedBy (extractAssignment S) := by
  intro j hj
  have hdep_root : ((SATRedName.root, SATRedVersion.unit), SATRedName.clause j,
      {SATRedVersion.lit (φ j).l₁, SATRedVersion.lit (φ j).l₂,
       SATRedVersion.lit (φ j).l₃}) ∈ satRedDeps φ clauses := by
    simp only [satRedDeps, Finset.mem_union, Finset.mem_image]
    left; exact ⟨j, hj, rfl⟩
  obtain ⟨cv, hcv_mem, hcv_S⟩ := hres.dep_closure _ hres.root_mem _ _ hdep_root
  unfold ThreeClause.satisfiedBy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcv_mem
  have step : ∀ (li : Literal Var),
      li ∈ ({(φ j).l₁, (φ j).l₂, (φ j).l₃} : Finset _) →
      (SATRedName.clause j, SATRedVersion.lit li) ∈ S →
      li.eval (extractAssignment S) = true := by
    intro li _ hli_S
    have hdep_cl : ((SATRedName.clause j, SATRedVersion.lit li),
        SATRedName.var li.var,
        ({SATRedVersion.bool li.pos} : Finset _)) ∈ satRedDeps φ clauses := by
      simp only [satRedDeps, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_insert, Finset.mem_singleton]
      right
      simp only [Finset.mem_insert, Finset.mem_singleton] at *
      exact ⟨j, hj, li, ‹_›, rfl⟩
    obtain ⟨vv, hvv_mem, hvv_S⟩ := hres.dep_closure _ hli_S _ _ hdep_cl
    rw [Literal.eval_true_iff]
    exact extractAssignment_spec ((Finset.mem_singleton.mp hvv_mem) ▸ hvv_S) hres.version_unique
  rcases hcv_mem with heq | heq | heq
  · exact Or.inl (step _ (by simp) (heq ▸ hcv_S))
  · exact Or.inr (Or.inl (step _ (by simp) (heq ▸ hcv_S)))
  · exact Or.inr (Or.inr (step _ (by simp) (heq ▸ hcv_S)))

end PackageCalculus.Complexity