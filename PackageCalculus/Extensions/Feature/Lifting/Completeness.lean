import PackageCalculus.Extensions.Feature.Lifting.Definition

namespace PackageCalculus.Feature

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {F : Type*} [DecidableEq F] [Fintype F]
variable {N' : Type*} [DecidableEq N'] [hfn : HasFeatureNames N F N']

theorem liftResolution_completenessWitness
    (S_f : Finset (Package N V × Finset F))
    (hfu : ∀ n v v' fs fs', ((n, v), fs) ∈ S_f → ((n, v'), fs') ∈ S_f → fs = fs') :
    liftResolution (hfn := hfn) (completenessWitness S_f) = S_f := by
  ext ⟨⟨pn, pv⟩, fs⟩
  constructor
  · -- forward: ∈ liftResolution → ∈ S_f
    intro h
    obtain ⟨n, v, horig, heq⟩ := liftResolution_elim h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, hfs_eq⟩ := heq
    -- horig : (origN pn, pv) ∈ completenessWitness S_f
    simp only [completenessWitness, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at horig
    rcases horig with ⟨⟨⟨n', v'⟩, fs'⟩, hmem, heq'⟩ | ⟨⟨⟨n', v'⟩, fs'⟩, hmem', hfmem⟩
    · simp only [Prod.mk.injEq] at heq'
      obtain ⟨h1, h2⟩ := heq'
      have hn := hfn.origN.injective h1
      subst hn; subst h2
      suffices hfs : fs = fs' by subst hfs; exact hmem
      rw [hfs_eq]; ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hf
        simp only [completenessWitness, Finset.mem_union, Finset.mem_image,
          Finset.mem_biUnion] at hf
        rcases hf with ⟨⟨⟨n₀, v₀⟩, fs₀⟩, _, heq''⟩ |
            ⟨⟨⟨n₀, v₀⟩, fs₀⟩, hmem₀, hfmem'⟩
        · simp only [Prod.mk.injEq] at heq''
          exact absurd heq''.1 (hfn.origN_ne_featuredN _ _ _)
        · obtain ⟨f', hf', heq''⟩ := hfmem'
          simp only [Prod.mk.injEq] at heq''
          obtain ⟨h1, rfl⟩ := heq''
          obtain ⟨rfl, rfl⟩ := hfn.featuredN_injective h1
          exact hfu _ _ _ _ _ hmem hmem₀ ▸ hf'
      · intro hf
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
          ⟨⟨(n', v'), fs'⟩, hmem, Finset.mem_image.mpr ⟨f, hf, rfl⟩⟩))
    · -- origN pn = featuredN ... contradiction
      obtain ⟨f', _, heq'⟩ := hfmem
      simp only [Prod.mk.injEq] at heq'
      exact absurd heq'.1.symm (hfn.origN_ne_featuredN _ _ _)
  · -- backward: ∈ S_f → ∈ liftResolution
    intro hmem
    have horig : (hfn.origN pn, pv) ∈ completenessWitness (N' := N') S_f :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨⟨(pn, pv), fs⟩, hmem, rfl⟩))
    have h := mem_liftResolution' horig
    convert h using 1
    simp only [Prod.mk.injEq, true_and]
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hf
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨⟨(pn, pv), fs⟩, hmem, Finset.mem_image.mpr ⟨f, hf, rfl⟩⟩))
    · intro hf
      simp only [completenessWitness, Finset.mem_union, Finset.mem_image,
        Finset.mem_biUnion] at hf
      rcases hf with ⟨⟨⟨n₀, v₀⟩, fs₀⟩, _, heq'⟩ | ⟨⟨⟨n₀, v₀⟩, fs₀⟩, hmem', hfmem'⟩
      · simp only [Prod.mk.injEq] at heq'
        exact absurd heq'.1 (hfn.origN_ne_featuredN _ _ _)
      · obtain ⟨f', hf', heq'⟩ := hfmem'
        simp only [Prod.mk.injEq] at heq'
        obtain ⟨h1, rfl⟩ := heq'
        obtain ⟨rfl, rfl⟩ := hfn.featuredN_injective h1
        exact hfu _ _ _ _ _ hmem hmem' ▸ hf'

theorem liftResolution_completeness
    (R_f : Real N V) (support : Support N V F)
    (Δ_f : FeatDepRel N V F) (Δ_a : AddlDepRel N V F)
    (r : Package N V)
    (S_f : Finset (Package N V × Finset F))
    (hres : IsFeatureResolution R_f support Δ_f Δ_a r S_f) :
    ∃ S', IsResolution (featureReal R_f support) (featureDeps R_f support Δ_f Δ_a)
      (embedPkg F r) S' ∧ liftResolution S' = S_f :=
  ⟨completenessWitness S_f, feature_completeness R_f support Δ_f Δ_a r S_f hres,
   liftResolution_completenessWitness S_f hres.feature_unification⟩


end PackageCalculus.Feature
