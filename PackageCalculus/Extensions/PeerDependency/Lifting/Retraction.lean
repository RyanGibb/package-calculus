import PackageCalculus.Extensions.PeerDependency.Lifting.Definition

namespace PackageCalculus.PeerDep

open PackageCalculus Concurrent

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {G : Type*} [DecidableEq G]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

/-! ## Round-trip theorems -/

theorem liftReal_peerReal (R : Real N V) (Δ : DepRel N V)
    (Θ : PeerRel N V) (g : V → G) :
    liftReal g (peerReal (N' := N') (V' := V') R Δ Θ g) = R := by
  ext p
  simp only [mem_liftReal, peerReal, Concurrent.embedReal, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion]
  constructor
  · intro h
    rcases h with ((⟨q, hqR, heq⟩ | ⟨a, _, hmem⟩) | ⟨a, _, hmem⟩)
    · simp only [Concurrent.embedPkg, Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      have ⟨hn, _⟩ := hcnm.granularN_injective h1
      have hv := hcvr.origV.injective h2
      exact (Prod.ext hn hv : q = p) ▸ hqR
    · obtain ⟨⟨n, v⟩, m, vs⟩ := a
      simp only [Concurrent.embedPkg, Prod.mk.injEq] at hmem
      obtain ⟨_, _, ⟨h1, _⟩⟩ := hmem
      exact absurd h1 (hcnm.intermediateN_ne_granularN _ _ _ _ _)
    · obtain ⟨⟨n, v⟩, o, us⟩ := a
      simp only [Finset.mem_filter] at hmem
      obtain ⟨u_peer, _, theta_entry, ⟨_, _⟩, hmem'⟩ := hmem
      obtain ⟨_, _, _⟩ := theta_entry
      simp only [Concurrent.embedPkg, Prod.mk.injEq] at hmem'
      obtain ⟨_, _, ⟨h1, _⟩⟩ := hmem'
      exact absurd h1 (hcnm.intermediateN_ne_granularN _ _ _ _ _)
  · intro hp
    exact Or.inl (Or.inl ⟨p, hp, rfl⟩)


end PackageCalculus.PeerDep
