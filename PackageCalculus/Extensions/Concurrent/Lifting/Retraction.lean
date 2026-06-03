import PackageCalculus.Extensions.Concurrent.Lifting.Definition

namespace PackageCalculus.Concurrent

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {G : Type*} [DecidableEq G]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

/-! ## Round-trip theorems -/

theorem liftReal_concurrentReal (R : Real N V) (Δ : DepRel N V) (g : V → G) :
    liftReal g (concurrentReal (N' := N') (V' := V') R Δ g) = R := by
  ext p
  simp only [mem_liftReal, concurrentReal, embedReal, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion]
  constructor
  · intro h
    rcases h with ⟨q, hqR, heq⟩ | ⟨a, haΔ, hmem⟩
    · simp only [embedPkg, Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      have ⟨hn, _⟩ := hcnm.granularN_injective h1
      have hv := hcvr.origV.injective h2
      exact (Prod.ext hn hv : q = p) ▸ hqR
    · obtain ⟨⟨n, v⟩, m, vs⟩ := a
      simp only at hmem
      split at hmem
      · simp only [Finset.mem_image, embedPkg, Prod.mk.injEq] at hmem
        obtain ⟨_, _, ⟨heq, _⟩⟩ := hmem
        exact absurd heq.symm (hcnm.granularN_ne_intermediateN _ _ _ _ _)
      · exact (List.mem_nil_iff _).mp hmem |>.elim
  · intro hp
    exact Or.inl ⟨p, hp, rfl⟩


end PackageCalculus.Concurrent
