import PackageCalculus.Extensions.Feature.Reduction.Definition

/-! # Feature extension: completeness

Any feature resolution lifts to a core resolution of the feature encoding. -/

namespace PackageCalculus.Feature

open Classical

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {F : Type*} [DecidableEq F]
variable {N' : Type*} [DecidableEq N'] [hfn : HasFeatureNames N F N']

def completenessWitness (S_f : Finset (Package N V × Finset F)) :
    Finset (Package N' V) :=
  -- Base packages
  S_f.image (fun ⟨⟨n, v⟩, _⟩ => (hfn.origN n, v)) ∪
  -- Feature packages
  S_f.biUnion (fun ⟨⟨n, v⟩, fs⟩ =>
    fs.image (fun f => (hfn.featuredN n f, v)))

-- Paper Thm 4.4.6 (Feature Reduction Completeness).
theorem feature_completeness
    (R_f : Real N V) (support : Support N V F)
    (Δ_f : FeatDepRel N V F) (Δ_a : AddlDepRel N V F)
    (r : Package N V)
    (S_f : Finset (Package N V × Finset F))
    (hres : IsFeatureResolution R_f support Δ_f Δ_a r S_f) :
    IsResolution (featureReal R_f support) (featureDeps R_f support Δ_f Δ_a)
      (embedPkg F r) (completenessWitness S_f) := by
  have mem_base : ∀ n v fs, ((n, v), fs) ∈ S_f →
      (hfn.origN n, v) ∈ completenessWitness S_f := by
    intro n v fs h
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨⟨(n, v), fs⟩, h, rfl⟩))
  have mem_feat : ∀ n v fs f, ((n, v), fs) ∈ S_f → f ∈ fs →
      (hfn.featuredN n f, v) ∈ completenessWitness S_f := by
    intro n v fs f h hf
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
      ⟨⟨(n, v), fs⟩, h, Finset.mem_image.mpr ⟨f, hf, rfl⟩⟩))
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- subset
    intro q hq
    simp only [completenessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hq
    simp only [featureReal, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, embedSet,
      embedPkg]
    rcases hq with (⟨⟨⟨n, v⟩, fs⟩, hmem, rfl⟩ | ⟨⟨⟨n, v⟩, fs⟩, hmem, hfmem⟩)
    · left; exact ⟨(n, v), hres.subset (n, v) fs hmem, rfl⟩
    · obtain ⟨f, hf, rfl⟩ := hfmem
      right
      refine ⟨⟨(n, v), f⟩, hres.support_mem n v fs f hmem hf, ?_⟩
      simp [hres.subset (n, v) fs hmem]
  · -- root_mem
    exact mem_base r.1 r.2 ∅ hres.root_mem
  · -- dep_closure
    intro q hq m ws hd
    simp only [completenessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hq
    rcases hq with (⟨⟨⟨pn, pv⟩, fs⟩, hmem, rfl⟩ | ⟨⟨⟨pn, pv⟩, fs⟩, hmem, hfmem⟩)
    · -- base package (origN pn, pv)
      simp only [featureDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
        Finset.mem_filter] at hd
      rcases hd with ((((⟨⟨⟨n', v'⟩, f'⟩, _, ha_ite⟩ |
          ⟨⟨p, m', vs', fs₀⟩, ⟨hdf, hfs_eq⟩, heq⟩) |
          ⟨⟨p, m', vs', fs'⟩, ⟨hdf, _⟩, hfm⟩) |
          ⟨⟨⟨pnv, f'⟩, m', vs', _⟩, ⟨_, _⟩, heq⟩) |
          ⟨⟨⟨pnv, f'⟩, m', vs', fs'⟩, ⟨_, _⟩, hfm⟩)
      · -- (4.4.4.2a): source is featuredN → contradiction
        split at ha_ite
        · simp only [Finset.mem_singleton, Prod.mk.injEq] at ha_ite
          exact absurd ha_ite.1.1 (by simp)
        · simp at ha_ite
      · -- (4.4.4.2b) no features
        simp only [embedPkg, Prod.mk.injEq] at heq
        obtain ⟨⟨h1, h2⟩, rfl, rfl⟩ := heq
        have h1' := hfn.origN.injective h1; subst h1'; subst h2
        subst hfs_eq
        obtain ⟨v', hv', fs', _, hfs'⟩ :=
          hres.feat_dep_closure p fs hmem m' vs' ∅ hdf
        exact ⟨v', hv', mem_base m' v' fs' hfs'⟩
      · -- (4.4.4.2b) with features
        obtain ⟨f', hf', heq⟩ := hfm
        simp only [embedPkg, Prod.mk.injEq] at heq
        obtain ⟨⟨h1, h2⟩, rfl, rfl⟩ := heq
        have h1' := hfn.origN.injective h1; subst h1'; subst h2
        obtain ⟨v', hv', fs'', hfs_sub, hfs''⟩ :=
          hres.feat_dep_closure p fs hmem m' vs' fs' hdf
        exact ⟨v', hv', mem_feat m' v' fs'' f' hfs'' (hfs_sub hf')⟩
      · -- (4.4.4.2c) no features: source is featuredN → contradiction
        simp only [Prod.mk.injEq] at heq; exact absurd heq.1.1 (by simp)
      · -- (4.4.4.2c) with features: source is featuredN → contradiction
        obtain ⟨f'', _, heq⟩ := hfm
        simp only [Prod.mk.injEq] at heq; exact absurd heq.1.1 (by simp)
    · -- featured package (featuredN pn f₀, pv)
      obtain ⟨f₀, hf₀, rfl⟩ := hfmem
      simp only [featureDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
        Finset.mem_filter] at hd
      rcases hd with ((((⟨⟨⟨n', v'⟩, f'⟩, _, ha_ite⟩ |
          ⟨⟨p, m', vs', _⟩, ⟨_, _⟩, heq⟩) |
          ⟨⟨p, m', vs', fs'⟩, ⟨_, _⟩, hfm⟩) |
          ⟨⟨⟨pnv, f'⟩, m', vs', fs₀⟩, ⟨hda, hfs_eq⟩, heq⟩) |
          ⟨⟨⟨pnv, f'⟩, m', vs', fs'⟩, ⟨hda, _⟩, hfm⟩)
      · -- (4.4.4.2a): (featuredN n' f', v') → (origN n', {v'})
        split at ha_ite
        · simp only [Finset.mem_singleton, Prod.mk.injEq] at ha_ite
          obtain ⟨⟨h1, h2⟩, rfl, rfl⟩ := ha_ite
          obtain ⟨rfl, rfl⟩ := hfn.featuredN_injective h1; subst h2
          exact ⟨pv, Finset.mem_singleton.mpr rfl, mem_base pn pv fs hmem⟩
        · simp at ha_ite
      · -- (4.4.4.2b): source is embedPkg = origN → contradiction
        simp only [embedPkg, Prod.mk.injEq] at heq; exact absurd heq.1.1 (by simp)
      · -- (4.4.4.2b) with features: source is embedPkg → contradiction
        obtain ⟨f', _, heq⟩ := hfm
        simp only [embedPkg, Prod.mk.injEq] at heq; exact absurd heq.1.1 (by simp)
      · -- (4.4.4.2c) no features: (featuredN n' f', v') → (origN m', vs')
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨h1, h2⟩, rfl, rfl⟩ := heq
        obtain ⟨hn_eq, hf_eq⟩ := hfn.featuredN_injective h1
        subst hn_eq; subst hf_eq; subst h2; subst hfs_eq
        obtain ⟨v', hv', fs', _, hfs'⟩ :=
          hres.addl_dep_closure (pnv.1, pnv.2) fs hmem f' hf₀ m' vs' ∅ hda
        exact ⟨v', hv', mem_base m' v' fs' hfs'⟩
      · -- (4.4.4.2c) with features: (featuredN n' f', v') → (featuredN m' f'', vs')
        obtain ⟨f'', hf'', heq⟩ := hfm
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨h1, h2⟩, rfl, rfl⟩ := heq
        obtain ⟨hn_eq, hf_eq⟩ := hfn.featuredN_injective h1
        subst hn_eq; subst hf_eq; subst h2
        obtain ⟨v', hv', fs'', hfs_sub, hfs''⟩ :=
          hres.addl_dep_closure (pnv.1, pnv.2) fs hmem f' hf₀ m' vs' fs' hda
        exact ⟨v', hv', mem_feat m' v' fs'' f'' hfs'' (hfs_sub hf'')⟩
  · -- version_unique
    intro nm v1 v2 hv1 hv2
    simp only [completenessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hv1 hv2
    rcases hv1 with (⟨⟨⟨n₁, _⟩, fs₁⟩, hmem₁, heq1⟩ | ⟨⟨⟨n₁, _⟩, fs₁⟩, hmem₁, hfmem1⟩) <;>
    rcases hv2 with (⟨⟨⟨n₂, _⟩, fs₂⟩, hmem₂, heq2⟩ | ⟨⟨⟨n₂, _⟩, fs₂⟩, hmem₂, hfmem2⟩)
    · -- origN × origN
      simp only [Prod.mk.injEq] at heq1 heq2
      obtain ⟨h1n, rfl⟩ := heq1; obtain ⟨h2n, rfl⟩ := heq2
      exact hres.version_unique n₁ _ _ fs₁ fs₂ hmem₁
        (hfn.origN.injective (h1n.trans h2n.symm) ▸ hmem₂)
    · -- origN × featuredN: name clash
      simp only [Prod.mk.injEq] at heq1
      obtain ⟨h1n, rfl⟩ := heq1
      obtain ⟨f₂, _, heq2⟩ := hfmem2
      simp only [Prod.mk.injEq] at heq2
      exact absurd (h1n.trans heq2.1.symm) (by simp)
    · -- featuredN × origN: name clash
      obtain ⟨f₁, _, heq1⟩ := hfmem1
      simp only [Prod.mk.injEq] at heq1 heq2
      exact absurd (heq1.1.trans heq2.1.symm) (by simp)
    · -- featuredN × featuredN
      obtain ⟨f₁, _, heq1⟩ := hfmem1
      obtain ⟨f₂, _, heq2⟩ := hfmem2
      simp only [Prod.mk.injEq] at heq1 heq2
      obtain ⟨h1n, rfl⟩ := heq1; obtain ⟨h2n, rfl⟩ := heq2
      obtain ⟨rfl, rfl⟩ := hfn.featuredN_injective (h1n.trans h2n.symm)
      exact hres.version_unique n₁ _ _ fs₁ fs₂ hmem₁ hmem₂

end PackageCalculus.Feature
