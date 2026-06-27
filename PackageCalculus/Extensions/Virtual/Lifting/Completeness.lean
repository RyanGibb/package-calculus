import PackageCalculus.Extensions.Virtual.Lifting.Definition

namespace PackageCalculus.Virtual

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVirtualNames N V N'] [hvv : HasVirtualVersions N V V']

theorem liftResolution_completenessWitness
    (Delta_v : DepRel N V) (prov : ProvidesRel N V)
    (S_v : Finset (Package N V))
    (rho : Finset (Package N V × N × Package N V)) :
    liftResolution (completenessWitness Delta_v prov S_v rho) = S_v := by
  ext p
  simp only [mem_liftResolution, completenessWitness, embedSet, Finset.mem_union,
    Finset.mem_image, Finset.mem_biUnion, Finset.mem_filter, embedPkg]
  constructor
  · intro h
    rcases h with ⟨q, hqS, heq⟩ | ⟨⟨p', n, vs⟩, ⟨_, _⟩, hmem⟩
    · simp only [Prod.mk.injEq] at heq
      exact (Prod.ext (hvn.origN.injective heq.1) (hvv.origV.injective heq.2) : q = p) ▸ hqS
    · split at hmem
      · rw [Finset.mem_singleton] at hmem
        simp only [Prod.mk.injEq] at hmem
        exact absurd hmem.1 (hvn.origN_ne_selectorN _ _ _)
      · simp at hmem
  · intro hp
    exact Or.inl ⟨p, hp, rfl⟩

theorem liftResolution_completeness
    (R_v : Real N V) (Delta_v : DepRel N V)
    (prov : ProvidesRel N V) (r : Package N V)
    (S_v : Finset (Package N V))
    (rho : Finset (Package N V × N × Package N V))
    (hres : IsVirtualResolution R_v Delta_v prov r S_v rho)
    (hfunc : Delta_v.FunctionalInName) :
    ∃ S', IsResolution (virtualReal R_v Delta_v prov) (virtualDeps Delta_v R_v prov)
      (embedPkg r) S' ∧ liftResolution S' = S_v :=
  ⟨completenessWitness Delta_v prov S_v rho,
   virtual_completeness R_v Delta_v prov r S_v rho hres hfunc,
   liftResolution_completenessWitness Delta_v prov S_v rho⟩


end PackageCalculus.Virtual
