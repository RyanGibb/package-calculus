import PackageCalculus.Extensions.Conflict.Lifting.Definition

namespace PackageCalculus.Conflict

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcn : HasConflictNames N V N'] [hcv : HasConflictVersions V V']

/-! ## Round-trip theorems -/

theorem liftReal_conflictReal (R : Real N V) (Γ : ConflictRel N V) :
    liftReal (conflictReal R Γ) = R := by
  ext p
  simp only [mem_liftReal, conflictReal, embedSet, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion]
  constructor
  · intro h
    rcases h with ⟨q, hqR, heq⟩ | ⟨a, haΓ, hmem⟩
    · simp only [embedPkg, Prod.mk.injEq] at heq
      have h1 := hcn.origN.injective heq.1; have h2 := hcv.origV.injective heq.2
      exact (Prod.ext h1 h2 : q = p) ▸ hqR
    · simp only [Finset.mem_insert, Finset.mem_singleton, embedPkg, Prod.mk.injEq] at hmem
      rcases hmem with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact absurd h1 (hcn.origN_ne_syntheticN _ _ _)
  · intro hp
    exact Or.inl ⟨p, hp, rfl⟩

theorem liftDeps_conflictDeps (Δ : DepRel N V) (Γ : ConflictRel N V) :
    liftDeps (conflictDeps Δ Γ) = Δ := by
  ext ⟨p, m, vs⟩;
  rw [ mem_liftDeps ];
  simp +decide [ embedDepFn, conflictDeps ];
  simp +decide [ embedPkg, embedVS ]

theorem liftConflicts_conflictDeps (Δ : DepRel N V) (Γ : ConflictRel N V) :
    liftConflicts (conflictDeps Δ Γ) = Γ := by
  refine' Finset.Subset.antisymm _ _;
  · intro c hc;
    obtain ⟨d, hd, hcd⟩ : ∃ d, d ∈ conflictDeps Δ Γ ∧ conflictDepFn c = d := by
      grind +suggestions;
    subst hcd;
    unfold conflictDepFn at hd; simp +decide [ conflictDeps ] at hd;
    obtain ⟨ a, b, a_1, b_1, h₁, h₂, h₃ ⟩ := hd; have := hcn.syntheticN_injective h₃; simp_all +decide ;
    unfold embedPkg at h₂; aesop;
  · intro c hc
    rw [mem_liftConflicts]
    simp [conflictDeps, conflictDepFn];
    exact ⟨ _, _, _, _, hc, rfl, rfl ⟩

theorem conflictLift_conflictReduce (R : Real N V) (Δ : DepRel N V) (Γ : ConflictRel N V) :
    conflictLift (conflictReduce R Δ Γ).1 (conflictReduce R Δ Γ).2 = (R, Δ, Γ) := by
  simp only [conflictLift, conflictReduce,
    liftReal_conflictReal, liftDeps_conflictDeps, liftConflicts_conflictDeps]

end PackageCalculus.Conflict