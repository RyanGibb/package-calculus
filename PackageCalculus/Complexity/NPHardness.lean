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
  unfold selectLiteral
  simp only [Finset.mem_insert, Finset.mem_singleton]
  split_ifs
  · left; rfl
  · right; left; rfl
  · right; right; rfl

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

-- Paper Appendix A (3SAT reduction, soundness).
theorem satRed_soundness
    (φ : Cls → ThreeClause Var) (clauses : Finset Cls) (σ : Var → Bool)
    (hsat : ∀ j ∈ clauses, (φ j).satisfiedBy σ) :
    IsResolution (satRedReal φ clauses) (satRedDeps φ clauses)
      (SATRedName.root, SATRedVersion.unit) (soundnessWitness σ φ clauses) := by
  constructor
  · -- subset
    intro p hp
    simp only [soundnessWitness, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_insert] at hp
    rcases hp with ((hp | ⟨j, hj, l, hl, hp⟩) | ⟨j, hj, hp⟩)
    · -- root: p = (root, unit)
      rw [hp]
      exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_singleton.mpr rfl))
    · -- var: (var l.var, bool (σ l.var)) = p
      rw [← hp]
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨j, hj, Finset.mem_biUnion.mpr ⟨l, by
        simp only [Finset.mem_insert, Finset.mem_singleton]; exact hl,
        by cases (σ l.var) <;> simp⟩⟩
    · -- clause: (clause j, lit (selectLiteral ...)) = p
      rw [← hp]
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine ⟨j, hj, ?_⟩
      have hmem := selectLiteral_mem σ (φ j)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
      rcases hmem with h | h | h <;> simp [h]
  · -- root_mem
    show (SATRedName.root, SATRedVersion.unit) ∈ soundnessWitness σ φ clauses
    unfold soundnessWitness
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr rfl))
  · -- dep_closure
    intro p hp m vs hd
    simp only [satRedDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
      Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with ⟨j, hj, heq⟩ | ⟨j, hj, l, hl, heq⟩
    · -- root → clause dependency
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
      refine ⟨SATRedVersion.lit (selectLiteral σ (φ j)), ?_, ?_⟩
      · have hmem := selectLiteral_mem σ (φ j)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h | h
        · exact Or.inl (congrArg SATRedVersion.lit h)
        · exact Or.inr (Or.inl (congrArg SATRedVersion.lit h))
        · exact Or.inr (Or.inr (congrArg SATRedVersion.lit h))
      · simp only [soundnessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
        right; exact ⟨j, hj, rfl⟩
    · -- clause → variable dependency
      -- heq : ((clause j, lit l), var l.var, {bool l.pos}) = (p, m, vs)
      -- after Prod.mk.injEq, obtain substitutes p, m, vs
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
      refine ⟨SATRedVersion.bool l.pos, Finset.mem_singleton.mpr rfl, ?_⟩
      -- hp says (clause j, lit l) ∈ soundnessWitness
      simp only [soundnessWitness, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
        Finset.mem_image, Finset.mem_insert] at hp
      -- From mem_image, the clause case gives: ∃ j' ∈ clauses, (clause j', lit (sel σ (φ j'))) = (clause j, lit l)
      rcases hp with ((h | ⟨_, _, _, _, h⟩) | ⟨j', hj', h⟩)
      · exact nomatch congrArg (·.1) h
      · exact nomatch congrArg (·.1) h
      · -- h : (clause j', lit (selectLiteral σ (φ j'))) = (clause j, lit l)
        have hj_eq : j' = j := SATRedName.clause.inj (congrArg (·.1) h)
        have hl_eq : selectLiteral σ (φ j') = l := SATRedVersion.lit.inj (congrArg (·.2) h)
        -- l.eval σ = true since l = selectLiteral σ (φ j') and clause j' is satisfied
        have heval_l : l.eval σ = true := by
          rw [← hl_eq]; exact selectLiteral_eval (hsat j' hj')
        rw [Literal.eval_true_iff] at heval_l
        -- Need to show (var l.var, bool l.pos) ∈ soundnessWitness
        simp only [soundnessWitness, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
          Finset.mem_image, Finset.mem_insert]
        left; right
        -- Use j' (= j) and l, which is the selectLiteral, hence in the literal finset
        have hl_mem : l ∈ ({(φ j').l₁, (φ j').l₂, (φ j').l₃} : Finset (Literal Var)) := by
          rw [← hl_eq]; exact selectLiteral_mem σ (φ j')
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl_mem
        exact ⟨j', hj', l, hl_mem, by rw [heval_l]⟩
  · -- version_unique
    intro n v v' hv hv'
    simp only [soundnessWitness, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_insert] at hv hv'
    -- hv patterns:
    --   root:   (n, v) = (root, unit)                     [from mem_singleton]
    --   var:    ∃ j hj l hl, (var l.var, bool (σ l.var)) = (n, v)  [from mem_image]
    --   clause: ∃ j hj, (clause j, lit ...) = (n, v)              [from mem_image]
    rcases hv with ((hv | ⟨_, _, _, _, hv⟩) | ⟨_, _, hv⟩)
    · -- (n,v) = (root, unit)
      rcases hv' with ((hv' | ⟨_, _, _, _, hv'⟩) | ⟨_, _, hv'⟩)
      · exact (congrArg (·.2) hv).trans (congrArg (·.2) hv').symm
      · -- root = var: hv gives n = root, hv' gives var _ = n
        exact nomatch (congrArg (·.1) hv').trans (congrArg (·.1) hv)
      · -- root = clause: hv gives n = root, hv' gives clause _ = n
        exact nomatch (congrArg (·.1) hv').trans (congrArg (·.1) hv)
    · -- (var l.var, bool (σ l.var)) = (n, v)
      rcases hv' with ((hv' | ⟨_, _, _, _, hv'⟩) | ⟨_, _, hv'⟩)
      · -- var = root: hv gives var _ = n, hv' gives n = root
        exact nomatch (congrArg (·.1) hv).trans (congrArg (·.1) hv')
      · -- var = var: both have (var _, bool _) = (n, _)
        have hv2 := congrArg (·.2) hv   -- bool (σ w₁.var) = v
        have hv2' := congrArg (·.2) hv'  -- bool (σ w₂.var) = v'
        have heq := SATRedName.var.inj ((congrArg (·.1) hv).trans (congrArg (·.1) hv').symm)
        simp only [heq] at hv2
        exact hv2.symm.trans hv2'
      · -- var = clause
        exact nomatch (congrArg (·.1) hv).trans (congrArg (·.1) hv').symm
    · -- (clause j, lit ...) = (n, v)
      rcases hv' with ((hv' | ⟨_, _, _, _, hv'⟩) | ⟨_, _, hv'⟩)
      · -- clause = root
        exact nomatch (congrArg (·.1) hv).trans (congrArg (·.1) hv')
      · -- clause = var
        exact nomatch (congrArg (·.1) hv).trans (congrArg (·.1) hv').symm
      · -- clause = clause
        have := SATRedName.clause.inj ((congrArg (·.1) hv).trans (congrArg (·.1) hv').symm)
        subst this; exact (congrArg (·.2) hv).symm.trans (congrArg (·.2) hv')

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

-- Paper Appendix A (3SAT reduction, completeness).
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
  rcases hcv_mem with heq | heq | heq
  · left
    have hdep_cl : ((SATRedName.clause j, SATRedVersion.lit (φ j).l₁),
        SATRedName.var (φ j).l₁.var,
        ({SATRedVersion.bool (φ j).l₁.pos} : Finset _)) ∈ satRedDeps φ clauses := by
      simp only [satRedDeps, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_insert, Finset.mem_singleton]
      right; exact ⟨j, hj, (φ j).l₁, Or.inl rfl, rfl⟩
    obtain ⟨vv, hvv_mem, hvv_S⟩ := hres.dep_closure _ (heq ▸ hcv_S) _ _ hdep_cl
    rw [Literal.eval_true_iff]
    exact extractAssignment_spec ((Finset.mem_singleton.mp hvv_mem) ▸ hvv_S) hres.version_unique
  · right; left
    have hdep_cl : ((SATRedName.clause j, SATRedVersion.lit (φ j).l₂),
        SATRedName.var (φ j).l₂.var,
        ({SATRedVersion.bool (φ j).l₂.pos} : Finset _)) ∈ satRedDeps φ clauses := by
      simp only [satRedDeps, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_insert, Finset.mem_singleton]
      right; exact ⟨j, hj, (φ j).l₂, Or.inr (Or.inl rfl), rfl⟩
    obtain ⟨vv, hvv_mem, hvv_S⟩ := hres.dep_closure _ (heq ▸ hcv_S) _ _ hdep_cl
    rw [Literal.eval_true_iff]
    exact extractAssignment_spec ((Finset.mem_singleton.mp hvv_mem) ▸ hvv_S) hres.version_unique
  · right; right
    have hdep_cl : ((SATRedName.clause j, SATRedVersion.lit (φ j).l₃),
        SATRedName.var (φ j).l₃.var,
        ({SATRedVersion.bool (φ j).l₃.pos} : Finset _)) ∈ satRedDeps φ clauses := by
      simp only [satRedDeps, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_insert, Finset.mem_singleton]
      right; exact ⟨j, hj, (φ j).l₃, Or.inr (Or.inr rfl), rfl⟩
    obtain ⟨vv, hvv_mem, hvv_S⟩ := hres.dep_closure _ (heq ▸ hcv_S) _ _ hdep_cl
    rw [Literal.eval_true_iff]
    exact extractAssignment_spec ((Finset.mem_singleton.mp hvv_mem) ▸ hvv_S) hres.version_unique

end PackageCalculus.Complexity
