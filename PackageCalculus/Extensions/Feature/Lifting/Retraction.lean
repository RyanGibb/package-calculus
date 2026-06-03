import PackageCalculus.Extensions.Feature.Lifting.Definition

namespace PackageCalculus.Feature

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {F : Type*} [DecidableEq F] [Fintype F]
variable {N' : Type*} [DecidableEq N'] [hfn : HasFeatureNames N F N']

/-! ## Round-trip theorem -/

omit [Fintype F] in
theorem liftReal_featureReal (R : Real N V) (support : Support N V F) :
    liftReal (hfn := hfn) (featureReal R support) = R := by
  ext p
  rw [mem_liftReal]
  simp only [featureReal, embedSet, embedPkg, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion]
  constructor
  · intro h
    rcases h with ⟨⟨qn, qv⟩, hqR, heq⟩ | ⟨a, _, hmem_ite⟩
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      have := hfn.origN.injective h1; subst this; subst h2
      exact hqR
    · split at hmem_ite
      · simp only [Finset.mem_singleton, Prod.mk.injEq] at hmem_ite
        exact absurd hmem_ite.1 (hfn.origN_ne_featuredN _ _ _)
      · simp at hmem_ite
  · intro hp
    exact Or.inl ⟨p, hp, rfl⟩


end PackageCalculus.Feature
