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
  ext ⟨p, m, vs⟩
  simp only [mem_liftDeps, conflictDeps, embedDepFn, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion]
  constructor
  · intro h
    rcases h with ((⟨a, hm, heq⟩ | ⟨a, hg, heq⟩) | ⟨a, hg, u, hu, heq⟩)
    · simp only [embedPkg, embedVS, Prod.mk.injEq] at heq
      obtain ⟨⟨h1, h2⟩, hm', hvs⟩ := heq
      have hp1 := hcn.origN.injective h1
      have hp2 := hcv.origV.injective h2
      have hmm := hcn.origN.injective hm'
      have hvs' : vs = a.2.2 := by
        ext v; constructor
        · intro hv
          have : hcv.origV v ∈ a.2.2.map hcv.origV :=
            hvs ▸ Finset.mem_map.mpr ⟨v, hv, rfl⟩
          obtain ⟨w, hw, hweq⟩ := Finset.mem_map.mp this
          exact hcv.origV.injective hweq ▸ hw
        · intro hv
          have : hcv.origV v ∈ vs.map hcv.origV :=
            hvs.symm ▸ Finset.mem_map.mpr ⟨v, hv, rfl⟩
          obtain ⟨w, hw, hweq⟩ := Finset.mem_map.mp this
          exact hcv.origV.injective hweq ▸ hw
      have hp := Prod.ext hp1 hp2
      subst hp hmm hvs'
      exact hm
    · simp only [embedPkg, Prod.mk.injEq] at heq
      exact absurd heq.2.1 (hcn.syntheticN_ne_origN _ _ _)
    · simp only [Prod.mk.injEq] at heq
      exact absurd heq.2.1 (hcn.syntheticN_ne_origN _ _ _)
  · intro hmem
    exact Or.inl (Or.inl ⟨⟨p, m, vs⟩, hmem, rfl⟩)

theorem liftConflicts_conflictDeps (Δ : DepRel N V) (Γ : ConflictRel N V) :
    liftConflicts (conflictDeps Δ Γ) = Γ := by
  ext ⟨p, n, vs⟩
  simp only [mem_liftConflicts, conflictDeps, conflictDepFn, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion]
  constructor
  · intro h
    rcases h with ((⟨a, hm, heq⟩ | ⟨a, hg, heq⟩) | ⟨a, hg, u, hu, heq⟩)
    · simp only [embedPkg, Prod.mk.injEq] at heq
      exact absurd heq.2.1 (hcn.origN_ne_syntheticN _ _ _)
    · simp only [embedPkg, Prod.mk.injEq] at heq
      obtain ⟨⟨h1, h2⟩, hsyn, _⟩ := heq
      have hp1 := hcn.origN.injective h1
      have hp2 := hcv.origV.injective h2
      obtain ⟨hn, hvs⟩ := hcn.syntheticN_injective hsyn
      have hp := Prod.ext hp1 hp2
      subst hp hn hvs
      exact hg
    · simp only [Prod.mk.injEq] at heq
      have hvs := heq.2.2
      have : hcv.oneV ∈ ({hcv.zeroV} : Finset V') := by
        rw [hvs]; exact Finset.mem_singleton.mpr rfl
      exact absurd (Finset.mem_singleton.mp this) hcv.oneV_ne_zeroV
  · intro hg
    exact Or.inl (Or.inr ⟨⟨p, n, vs⟩, hg, rfl⟩)

theorem conflictLift_conflictReduce (R : Real N V) (Δ : DepRel N V) (Γ : ConflictRel N V) :
    conflictLift (conflictReduce R Δ Γ).1 (conflictReduce R Δ Γ).2 = (R, Δ, Γ) := by
  simp only [conflictLift, conflictReduce,
    liftReal_conflictReal, liftDeps_conflictDeps, liftConflicts_conflictDeps]

end PackageCalculus.Conflict
