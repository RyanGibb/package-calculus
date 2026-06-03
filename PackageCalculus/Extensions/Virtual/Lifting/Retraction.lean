import PackageCalculus.Extensions.Virtual.Lifting.Definition

namespace PackageCalculus.Virtual

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVirtualNames N V N'] [hvv : HasVirtualVersions N V V']

/-! ## Round-trip theorems -/

theorem liftReal_virtualReal (R : Real N V) (Δ : DepRel N V)
    (prov : ProvidesRel N V) :
    liftReal (virtualReal (N' := N') (V' := V') R Δ prov) = R := by
  ext p
  simp only [mem_liftReal, virtualReal, embedSet, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion]
  constructor
  · intro h
    rcases h with ((⟨q, hqR, heq⟩ | ⟨a, _, hmem⟩) | ⟨a, _, hmem⟩)
    · exact (embedPkgFn_injective heq : q = p) ▸ hqR
    · -- Selector from provider biUnion
      exfalso
      obtain ⟨b, _, hmem'⟩ := hmem
      split at hmem'
      · rw [Finset.mem_singleton] at hmem'
        simp only [embedPkg, Prod.mk.injEq] at hmem'
        exact absurd hmem'.1 (hvn.origN_ne_selectorN _ _ _)
      · simp at hmem'
    · -- Selector from direct biUnion
      exfalso
      split at hmem
      · simp only [Finset.mem_image, Finset.mem_filter, embedPkg, Prod.mk.injEq] at hmem
        obtain ⟨_, _, ⟨h1, _⟩⟩ := hmem
        exact absurd h1 (hvn.selectorN_ne_origN _ _ _)
      · simp at hmem
  · intro hp
    exact Or.inl (Or.inl ⟨p, hp, rfl⟩)


end PackageCalculus.Virtual
