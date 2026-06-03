import PackageCalculus.Extensions.Conflict.Lifting.Definition

namespace PackageCalculus.Conflict

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcn : HasConflictNames N V N'] [hcv : HasConflictVersions V V']

theorem liftResolution_completenessWitness
    (S_Γ : Finset (Package N V)) (Γ : ConflictRel N V) :
    liftResolution (completenessWitness S_Γ Γ) = S_Γ := by
  ext p
  simp only [mem_liftResolution, completenessWitness, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, embedSet, embedPkg]
  constructor
  · intro h
    rcases h with ((⟨q, hqS, heq⟩ | ⟨⟨q, n, vs⟩, ⟨_, _⟩, heq⟩) |
        ⟨⟨q, n, vs⟩, ⟨_, _⟩, heq⟩)
    · simp only [Prod.mk.injEq] at heq
      have h1 := hcn.origN.injective heq.1; have h2 := hcv.origV.injective heq.2
      exact (Prod.ext h1 h2 : q = p) ▸ hqS
    · simp only [Prod.mk.injEq] at heq
      exact absurd heq.1 (hcn.syntheticN_ne_origN _ _ _)
    · simp only [Prod.mk.injEq] at heq
      exact absurd heq.1 (hcn.syntheticN_ne_origN _ _ _)
  · intro hp
    exact Or.inl (Or.inl ⟨p, hp, rfl⟩)

theorem liftResolution_completeness
    (R : Real N V) (Δ : DepRel N V) (Γ : ConflictRel N V)
    (r : Package N V) (S_Γ : Finset (Package N V))
    (hres : IsConflictResolution R Δ Γ r S_Γ) :
    ∃ S', IsResolution (conflictReal R Γ) (conflictDeps Δ Γ) (embedPkg r) S' ∧
          liftResolution S' = S_Γ :=
  ⟨completenessWitness S_Γ Γ, conflict_completeness R Δ Γ r S_Γ hres,
   liftResolution_completenessWitness S_Γ Γ⟩

end PackageCalculus.Conflict
