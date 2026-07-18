import PackageCalculus.Extensions.Feature.Reduction.Definition
import Mathlib.Data.Finset.Preimage

/-! # Feature extension: soundness

Any core resolution of the feature encoding induces a feature resolution of
the original problem. -/

namespace PackageCalculus.Feature

open Classical

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {F : Type*} [DecidableEq F] [Fintype F]
variable {N' : Type*} [DecidableEq N'] [hfn : HasFeatureNames N F N']

omit [DecidableEq N] [DecidableEq V] [DecidableEq F] [Fintype F]
    [DecidableEq N'] in
private theorem embedPkg_F_injective :
    Function.Injective (embedPkg F : Package N V → Package N' V) := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [embedPkg, Prod.mk.injEq] at h
  exact Prod.ext (hfn.origN.injective h.1) h.2

noncomputable def soundnessWitness
    (S : Finset (Package N' V)) : Finset (Package N V × Finset F) :=
  (S.preimage (embedPkg F) (Set.InjOn.mono (Set.subset_univ _)
    (Function.Injective.injOn embedPkg_F_injective))).image
    (fun p => (p, Finset.univ.filter (fun f => (hfn.featuredN p.1 f, p.2) ∈ S)))

private theorem mem_soundnessWitness {S : Finset (Package N' V)}
    {n : N} {v : V} (h : (hfn.origN n, v) ∈ S) :
    ((n, v), Finset.univ.filter (fun f => (hfn.featuredN n f, v) ∈ S)) ∈
      soundnessWitness S := by
  simp only [soundnessWitness, Finset.mem_image, Finset.mem_preimage, embedPkg]
  exact ⟨(n, v), h, rfl⟩

private theorem soundnessWitness_elim {S : Finset (Package N' V)}
    {pfs : Package N V × Finset F} (h : pfs ∈ soundnessWitness S) :
    ∃ n v, (hfn.origN n, v) ∈ S ∧
      pfs = ((n, v), Finset.univ.filter (fun f => (hfn.featuredN n f, v) ∈ S)) := by
  simp only [soundnessWitness, Finset.mem_image, Finset.mem_preimage, embedPkg] at h
  obtain ⟨⟨n, v⟩, hmem, rfl⟩ := h
  exact ⟨n, v, hmem, rfl⟩

theorem feature_soundness
    (R_f : Real N V) (support : Support N V F)
    (Δ_f : FeatDepRel N V F) (Δ_a : AddlDepRel N V F)
    (r : Package N V)
    (S : Finset (Package N' V))
    (hres : IsResolution (featureReal R_f support) (featureDeps R_f support Δ_f Δ_a)
      (embedPkg F r) S)
    (hroot_no_support : ∀ f, (r, f) ∉ support) :
    IsFeatureResolution R_f support Δ_f Δ_a r (soundnessWitness S) := by
  -- Derived: no feature package for the root is in S. Any such package would arise
  -- from a support entry (r, f), excluded by hroot_no_support.
  have hroot_no_feat : ∀ f, (hfn.featuredN r.1 f, r.2) ∉ S := by
    intro f hmem
    have hsub := hres.subset hmem
    simp only [featureReal, embedSet, embedPkg, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at hsub
    rcases hsub with ⟨⟨_, _⟩, _, heq⟩ | ⟨⟨⟨n', v'⟩, f'⟩, hsupp, hmem_ite⟩
    · simp only [Prod.mk.injEq] at heq
      exact absurd heq.1 (hfn.origN_ne_featuredN _ _ _)
    · split at hmem_ite
      · simp only [Finset.mem_singleton, Prod.mk.injEq] at hmem_ite
        obtain ⟨h1, rfl⟩ := hmem_ite
        obtain ⟨rfl, rfl⟩ := hfn.featuredN_injective h1
        exact hroot_no_support f hsupp
      · simp at hmem_ite
  -- Helper: (origN n, v) ∈ S → (n, v) ∈ R_f
  have orig_in_R : ∀ n v, (hfn.origN n, v) ∈ S → (n, v) ∈ R_f := by
    intro n v h
    have := hres.subset h
    simp only [featureReal, embedSet, embedPkg, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at this
    rcases this with ⟨⟨n', v'⟩, hR, heq⟩ | ⟨a, _, hmem_ite⟩
    · simp only [Prod.mk.injEq] at heq
      exact hfn.origN.injective heq.1 ▸ heq.2 ▸ hR
    · split at hmem_ite
      · simp only [Finset.mem_singleton, Prod.mk.injEq] at hmem_ite
        exact absurd hmem_ite.1 (hfn.origN_ne_featuredN _ _ _)
      · simp at hmem_ite
  -- Helper: (featuredN n f, v) ∈ S → (origN n, v) ∈ S
  have featured_orig : ∀ n f v, (hfn.featuredN n f, v) ∈ S →
      (hfn.origN n, v) ∈ S := by
    intro n f v h
    have hsub := hres.subset h
    simp only [featureReal, embedSet, embedPkg, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at hsub
    rcases hsub with ⟨⟨_, _⟩, _, heq⟩ | ⟨⟨⟨n', v'⟩, f'⟩, hsupp, hmem_ite⟩
    · simp only [Prod.mk.injEq] at heq; exact absurd heq.1 (hfn.origN_ne_featuredN _ _ _)
    · split at hmem_ite
      · rename_i hR
        simp only [Finset.mem_singleton, Prod.mk.injEq] at hmem_ite
        obtain ⟨h1, rfl⟩ := hmem_ite
        obtain ⟨rfl, rfl⟩ := hfn.featuredN_injective h1
        have hd : ((hfn.featuredN n f, v), hfn.origN n, ({v} : Finset V)) ∈
            featureDeps R_f support Δ_f Δ_a := by
          simp only [featureDeps, Finset.mem_union, Finset.mem_biUnion]
          left; left; left; left
          exact ⟨⟨(n, v), f⟩, hsupp, by simp [hR]⟩
        obtain ⟨v', hv', hv'S⟩ := hres.dep_closure _ h _ _ hd
        rw [Finset.mem_singleton.mp hv'] at hv'S
        exact hv'S
      · simp at hmem_ite
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- no_root_support
    exact hroot_no_support
  · -- subset
    intro ⟨pn, pv⟩ fs hmem
    obtain ⟨n, v, horig, heq⟩ := soundnessWitness_elim hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, _⟩ := heq
    exact orig_in_R pn pv horig
  · -- root_mem
    have hroot_in := mem_soundnessWitness (n := r.1) (v := r.2) hres.root_mem
    convert hroot_in using 1
    simp only [Prod.mk.injEq, Prod.eta, true_and]
    exact (Finset.filter_false_of_mem (fun f _ => hroot_no_feat f)).symm
  · -- feat_dep_closure
    intro ⟨pn, pv⟩ fs_p hmem_p n vs fs hdf
    obtain ⟨_, _, horig, heq₀⟩ := soundnessWitness_elim hmem_p
    simp only [Prod.mk.injEq] at heq₀
    obtain ⟨⟨rfl, rfl⟩, _⟩ := heq₀
    rcases Finset.eq_empty_or_nonempty fs with rfl | ⟨f₀, hf₀⟩
    · -- fs = ∅
      have hd : (embedPkg F (pn, pv), hfn.origN n, vs) ∈
          featureDeps R_f support Δ_f Δ_a := by
        simp only [featureDeps, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
        left; left; left; right
        exact ⟨⟨(pn, pv), n, vs, ∅⟩, ⟨hdf, rfl⟩, rfl⟩
      obtain ⟨v, hv, hvS⟩ := hres.dep_closure _ horig _ _ hd
      exact ⟨v, hv, _, Finset.empty_subset _, mem_soundnessWitness hvS⟩
    · -- fs nonempty
      have hd₀ : (embedPkg F (pn, pv), hfn.featuredN n f₀, vs) ∈
          featureDeps R_f support Δ_f Δ_a := by
        simp only [featureDeps, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image]
        left; left; right
        exact ⟨⟨(pn, pv), n, vs, fs⟩, ⟨hdf, ⟨f₀, hf₀⟩⟩, f₀, hf₀, rfl⟩
      obtain ⟨v, hv, hvS⟩ := hres.dep_closure _ horig _ _ hd₀
      have hvOrig := featured_orig n f₀ v hvS
      refine ⟨v, hv, _, ?_, mem_soundnessWitness hvOrig⟩
      intro f' hf'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hd' : (embedPkg F (pn, pv), hfn.featuredN n f', vs) ∈
          featureDeps R_f support Δ_f Δ_a := by
        simp only [featureDeps, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image]
        left; left; right
        exact ⟨⟨(pn, pv), n, vs, fs⟩, ⟨hdf, ⟨f₀, hf₀⟩⟩, f', hf', rfl⟩
      obtain ⟨v', _, hv'S⟩ := hres.dep_closure _ horig _ _ hd'
      rwa [hres.version_unique _ _ _ hvOrig (featured_orig n f' v' hv'S)]
  · -- addl_dep_closure
    intro ⟨pn, pv⟩ fs_p hmem_p f hf n vs fs hda
    obtain ⟨_, _, horig, heq₀⟩ := soundnessWitness_elim hmem_p
    simp only [Prod.mk.injEq] at heq₀
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq₀
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    change (hfn.featuredN pn f, pv) ∈ S at hf
    rcases Finset.eq_empty_or_nonempty fs with rfl | ⟨f₀, hf₀⟩
    · -- fs = ∅
      have hd : ((hfn.featuredN pn f, pv), hfn.origN n, vs) ∈
          featureDeps R_f support Δ_f Δ_a := by
        simp only [featureDeps, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
        left; right
        exact ⟨⟨⟨(pn, pv), f⟩, n, vs, ∅⟩, ⟨hda, rfl⟩, rfl⟩
      obtain ⟨v, hv, hvS⟩ := hres.dep_closure _ hf _ _ hd
      exact ⟨v, hv, _, Finset.empty_subset _, mem_soundnessWitness hvS⟩
    · -- fs nonempty
      have hd₀ : ((hfn.featuredN pn f, pv), hfn.featuredN n f₀, vs) ∈
          featureDeps R_f support Δ_f Δ_a := by
        simp only [featureDeps, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image]
        right
        exact ⟨⟨⟨(pn, pv), f⟩, n, vs, fs⟩, ⟨hda, ⟨f₀, hf₀⟩⟩, f₀, hf₀, rfl⟩
      obtain ⟨v, hv, hvS⟩ := hres.dep_closure _ hf _ _ hd₀
      have hvOrig := featured_orig n f₀ v hvS
      refine ⟨v, hv, _, ?_, mem_soundnessWitness hvOrig⟩
      intro f' hf'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hd' : ((hfn.featuredN pn f, pv), hfn.featuredN n f', vs) ∈
          featureDeps R_f support Δ_f Δ_a := by
        simp only [featureDeps, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image]
        right
        exact ⟨⟨⟨(pn, pv), f⟩, n, vs, fs⟩, ⟨hda, ⟨f₀, hf₀⟩⟩, f', hf', rfl⟩
      obtain ⟨v', _, hv'S⟩ := hres.dep_closure _ hf _ _ hd'
      rwa [hres.version_unique _ _ _ hvOrig (featured_orig n f' v' hv'S)]
  · -- feature_unification
    intro n v v' fs fs' hmem1 hmem2
    obtain ⟨_, _, horig1, heq1⟩ := soundnessWitness_elim hmem1
    obtain ⟨_, _, horig2, heq2⟩ := soundnessWitness_elim hmem2
    simp only [Prod.mk.injEq] at heq1 heq2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq1
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq2
    have := hres.version_unique _ _ _ horig1 horig2
    subst this; rfl
  · -- version_unique
    intro n v v' fs fs' hmem₁ hmem₂
    obtain ⟨_, _, horig₁, heq1⟩ := soundnessWitness_elim hmem₁
    obtain ⟨_, _, horig₂, heq2⟩ := soundnessWitness_elim hmem₂
    simp only [Prod.mk.injEq] at heq1 heq2
    obtain ⟨⟨rfl, rfl⟩, _⟩ := heq1
    obtain ⟨⟨h2n, rfl⟩, _⟩ := heq2
    exact hres.version_unique _ _ _ horig₁ (h2n ▸ horig₂)
  · -- support_mem
    intro n v fs f hmem hf
    obtain ⟨_, _, horig, heq⟩ := soundnessWitness_elim hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    change (hfn.featuredN n f, v) ∈ S at hf
    have hsub := hres.subset hf
    simp only [featureReal, embedSet, embedPkg, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at hsub
    rcases hsub with ⟨⟨_, _⟩, _, heq'⟩ | ⟨⟨⟨n', v'⟩, f'⟩, hsupp', hmem_ite⟩
    · simp only [Prod.mk.injEq] at heq'; exact absurd heq'.1 (hfn.origN_ne_featuredN _ _ _)
    · split at hmem_ite
      · simp only [Finset.mem_singleton, Prod.mk.injEq] at hmem_ite
        obtain ⟨h1, rfl⟩ := hmem_ite
        obtain ⟨rfl, rfl⟩ := hfn.featuredN_injective h1
        exact hsupp'
      · simp at hmem_ite

end PackageCalculus.Feature
