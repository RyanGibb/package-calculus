import PackageCalculus.Extensions.Conflict.Lifting.Definition

namespace PackageCalculus.Conflict

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcn : HasConflictNames N V N'] [hcv : HasConflictVersions V V']

/-! ## Lifting soundness & completeness -/

theorem liftResolution_soundness
    (R : Real N V) (Δ : DepRel N V) (Γ : ConflictRel N V)
    (r : Package N V) (S' : Finset (Package N' V'))
    (hres : IsResolution (conflictReal R Γ) (conflictDeps Δ Γ) (embedPkg r) S') :
    IsConflictResolution R Δ Γ r (liftResolution S') := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- subset
    intro p hp
    rw [mem_liftResolution] at hp
    have := hres.subset hp
    simp only [conflictReal, embedSet, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at this
    rcases this with ⟨q, hqR, heq⟩ | ⟨a, _, hmem⟩
    · simp only [embedPkg, Prod.mk.injEq] at heq
      exact (Prod.ext (hcn.origN.injective heq.1) (hcv.origV.injective heq.2) : q = p) ▸ hqR
    · simp only [Finset.mem_insert, Finset.mem_singleton, embedPkg, Prod.mk.injEq] at hmem
      rcases hmem with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact absurd h1 (hcn.origN_ne_syntheticN _ _ _)
  · -- root_mem
    rw [mem_liftResolution]; exact hres.root_mem
  · -- dep_closure
    intro p hp m vs hmem
    rw [mem_liftResolution] at hp
    have hd : (embedPkg p, hcn.origN m, embedVS vs) ∈ conflictDeps Δ Γ := by
      simp only [conflictDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
      exact Or.inl (Or.inl ⟨⟨p, m, vs⟩, hmem, rfl⟩)
    obtain ⟨v', hv'mem, hv'S⟩ := hres.dep_closure _ hp _ _ hd
    simp only [embedVS, Finset.mem_map] at hv'mem
    obtain ⟨v, hv, rfl⟩ := hv'mem
    exact ⟨v, hv, mem_liftResolution.mpr hv'S⟩
  · -- version_unique
    intro n v v' hv hv'
    rw [mem_liftResolution] at hv hv'
    exact hcv.origV.injective (hres.version_unique _ _ _ hv hv')
  · -- conflict_avoidance
    intro p hp n vs hg ⟨u, hu, humem⟩
    rw [mem_liftResolution] at hp humem
    have hd1 : (embedPkg p, hcn.syntheticN n vs, {hcv.oneV}) ∈ conflictDeps Δ Γ := by
      simp only [conflictDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
      exact Or.inl (Or.inr ⟨⟨p, n, vs⟩, hg, rfl⟩)
    obtain ⟨w, hw, hwS⟩ := hres.dep_closure _ hp _ _ hd1
    rw [Finset.mem_singleton] at hw; subst hw
    have hd2 : ((hcn.origN n, hcv.origV u), hcn.syntheticN n vs, {hcv.zeroV}) ∈ conflictDeps Δ Γ := by
      simp only [conflictDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
      exact Or.inr ⟨⟨_, n, vs⟩, hg, u, hu, rfl⟩
    obtain ⟨w', hw', hw'S⟩ := hres.dep_closure _ humem _ _ hd2
    rw [Finset.mem_singleton] at hw'; subst hw'
    have := hres.version_unique _ _ _ hwS hw'S
    exact absurd this hcv.oneV_ne_zeroV

end PackageCalculus.Conflict
