import PackageCalculus.Extensions.PeerDependency.Lifting.Definition

namespace PackageCalculus.PeerDep

open PackageCalculus Concurrent

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {G : Type*} [DecidableEq G]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

theorem liftResolution_completenessWitness (S_Θ : Finset (Package N V))
    (π : Finset (Package N V × Package N V))
    (Δ_C : DepRel N V) (g : V → G) :
    liftResolution g (completenessWitness S_Θ π Δ_C g) = S_Θ := by
  ext p
  simp only [mem_liftResolution, completenessWitness, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion, Concurrent.embedPkg]
  constructor
  · intro h
    rcases h with ⟨⟨n, v⟩, hqS, heq⟩ | ⟨a, haΔ, hmem⟩
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      have ⟨hn, _⟩ := hcnm.granularN_injective h1
      have hv := hcvr.origV.injective h2
      exact (Prod.ext hn hv : (n, v) = p) ▸ hqS
    · obtain ⟨⟨n, v⟩, m, vs⟩ := a
      simp only at hmem
      split at hmem
      case isTrue h =>
        simp only [Finset.mem_image, Finset.mem_filter, Prod.mk.injEq] at hmem
        obtain ⟨_, _, ⟨heq, _⟩⟩ := hmem
        exact absurd heq.symm (hcnm.granularN_ne_intermediateN _ _ _ _ _)
      case isFalse => exact (List.mem_nil_iff _ |>.mp hmem).elim
  · intro hp
    exact Or.inl ⟨p, hp, rfl⟩

theorem liftResolution_completeness
    (R_C : Real N V) (Δ_C : DepRel N V) (Θ : PeerRel N V)
    (g : V → G) (r : Package N V)
    (S_Θ : Finset (Package N V))
    (π : Finset (Package N V × Package N V))
    (hres : IsPeerResolution R_C Δ_C Θ g r S_Θ π)
    (hfunc : ∀ p m vs₁ vs₂, (p, m, vs₁) ∈ Δ_C → (p, m, vs₂) ∈ Δ_C → vs₁ = vs₂) :
    ∃ S', IsResolution (peerReal R_C Δ_C Θ g) (peerDeps Δ_C Θ g)
      (Concurrent.embedPkg g r) S' ∧ liftResolution g S' = S_Θ :=
  ⟨completenessWitness S_Θ π Δ_C g,
   peer_completeness R_C Δ_C Θ g r S_Θ π hres hfunc,
   liftResolution_completenessWitness S_Θ π Δ_C g⟩


end PackageCalculus.PeerDep
