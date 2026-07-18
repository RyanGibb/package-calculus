import PackageCalculus.Composition.FeatureConcurrent.Types
import PackageCalculus.Composition.FeatureConcurrent.Definition
import PackageCalculus.Composition.FeatureConcurrent.Reduction.Definition
import PackageCalculus.Extensions.Feature.Definition
import PackageCalculus.Extensions.Feature.Reduction.Definition
import PackageCalculus.Extensions.Feature.Reduction.Completeness
import PackageCalculus.Extensions.Concurrent.Definition
import PackageCalculus.Extensions.Concurrent.Reduction.Definition
import PackageCalculus.Extensions.Concurrent.Reduction.Completeness
import Mathlib

/-! # Feature-concurrent composition: completeness

Any `IsConcurrentFeatureResolution` lifts to a core resolution of the
feature-concurrent encoding, including the back-edges that align secondary
intermediates with the shared one. -/

namespace PackageCalculus.Composition

open Classical

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {F : Type*} [DecidableEq F] {G : Type*} [DecidableEq G]
variable {N_FC : Type*} [DecidableEq N_FC] {V_FC : Type*} [DecidableEq V_FC]
variable [hcnm : Concurrent.HasConcurrentNames (Feature.FeatureName N F) V G N_FC]
variable [hcvr : Concurrent.HasConcurrentVersions V G V_FC]
variable [hcfi : HasConcurrentFeatureIntermediate N V F G N_FC]

set_option linter.unusedSectionVars false

/-- Close any goal from an impossible equality between distinct synthetic-name
families (granular orig/featured, shared and secondary intermediates). -/
local macro "cf_name_clash " h:term : tactic =>
  `(tactic| first
      | (cases (hcnm.granularN_injective $h).1; done)
      | exact absurd $h (hcfi.cfIntermediateN_ne_granularN _ _ _ _ _)
      | exact absurd ($h).symm (hcfi.cfIntermediateN_ne_granularN _ _ _ _ _)
      | exact absurd $h (hcfi.cfIntermediateN_f_ne_granularN _ _ _ _ _ _)
      | exact absurd ($h).symm (hcfi.cfIntermediateN_f_ne_granularN _ _ _ _ _ _)
      | exact absurd $h (hcfi.cfIntermediateN_a_ne_granularN _ _ _ _ _ _ _)
      | exact absurd ($h).symm (hcfi.cfIntermediateN_a_ne_granularN _ _ _ _ _ _ _)
      | exact absurd $h (hcfi.cfIntermediateN_f_ne_cfIntermediateN _ _ _ _ _ _ _)
      | exact absurd ($h).symm (hcfi.cfIntermediateN_f_ne_cfIntermediateN _ _ _ _ _ _ _)
      | exact absurd $h (hcfi.cfIntermediateN_a_ne_cfIntermediateN _ _ _ _ _ _ _ _)
      | exact absurd ($h).symm (hcfi.cfIntermediateN_a_ne_cfIntermediateN _ _ _ _ _ _ _ _)
      | exact absurd $h (hcfi.cfIntermediateN_a_ne_cfIntermediateN_f _ _ _ _ _ _ _ _ _)
      | exact absurd ($h).symm (hcfi.cfIntermediateN_a_ne_cfIntermediateN_f _ _ _ _ _ _ _ _ _))

/-- Dismiss a witness case whose package equality is impossible by name family. -/
local macro "cf_clash " h:ident : tactic =>
  `(tactic| (simp only [Prod.mk.injEq] at $h:ident; cf_name_clash ($h).1))

/-- Completeness witness: builds the FC-level `S` from `(S_CF, π, Δ_f, Δ_a)`.

    * Each `((n, v), fs) ∈ S_CF` contributes its base orig granular package and its feature
      granular packages.
    * Each dep entry in `Δ_f` or `Δ_a` with `u ∈ vs`, `((m, u), _) ∈ S_CF`, and
      `((m, u), (n, v)) ∈ π` contributes the shared intermediate
      `(cfIntermediate n v m, origV u)`. -/
noncomputable def cfCompletenessWitness
    (S_CF : Finset (Package N V × Finset F))
    (π : Finset (Package N V × Package N V))
    (Δ_f : Feature.FeatDepRel N V F) (Δ_a : Feature.AddlDepRel N V F)
    (g : V → G) : Finset (Package N_FC V_FC) :=
  -- Part 1: base orig granular packages.
  S_CF.image (fun ⟨⟨n, v⟩, _⟩ =>
    (hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v)) ∪
  -- Part 2: feature granular packages.
  S_CF.biUnion (fun ⟨⟨n, v⟩, fs⟩ =>
    fs.image (fun f =>
      (hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v))) ∪
  -- Part 3: shared intermediates from Δ_f.
  Δ_f.biUnion (fun ⟨⟨n, v⟩, m, vs, fs⟩ =>
    (vs.filter (fun u =>
      (∃ fs_p, ((n, v), fs_p) ∈ S_CF) ∧
      (∃ fs', fs ⊆ fs' ∧ ((m, u), fs') ∈ S_CF) ∧
      ((m, u), (n, v)) ∈ π)).image
      (fun u => (hcfi.cfIntermediateN n v m, hcvr.origV u))) ∪
  -- Part 3b: shared intermediates from Δ_a.
  Δ_a.biUnion (fun ⟨⟨⟨n, v⟩, _⟩, m, vs, fs⟩ =>
    (vs.filter (fun u =>
      (∃ fs_p, ((n, v), fs_p) ∈ S_CF) ∧
      (∃ fs', fs ⊆ fs' ∧ ((m, u), fs') ∈ S_CF) ∧
      ((m, u), (n, v)) ∈ π)).image
      (fun u => (hcfi.cfIntermediateN n v m, hcvr.origV u))) ∪
  -- Part 4: per-feature Δ_f secondaries.
  Δ_f.biUnion (fun ⟨⟨n, v⟩, m, vs, fs⟩ =>
    fs.biUnion (fun f =>
      (vs.filter (fun u =>
        (∃ fs_p, ((n, v), fs_p) ∈ S_CF) ∧
        (∃ fs', fs ⊆ fs' ∧ ((m, u), fs') ∈ S_CF) ∧
        ((m, u), (n, v)) ∈ π)).image
        (fun u => (hcfi.cfIntermediateN_f n v m f, hcvr.origV u)))) ∪
  -- Part 5: per-feature Δ_a secondaries.
  Δ_a.biUnion (fun ⟨⟨⟨n, v⟩, f⟩, m, vs, fs⟩ =>
    fs.biUnion (fun f' =>
      (vs.filter (fun u =>
        (∃ fs_p, ((n, v), fs_p) ∈ S_CF) ∧
        (∃ fs', fs ⊆ fs' ∧ ((m, u), fs') ∈ S_CF) ∧
        ((m, u), (n, v)) ∈ π)).image
        (fun u => (hcfi.cfIntermediateN_a n v f m f', hcvr.origV u))))

/-! ### Witness Membership Helpers -/

theorem cfCompletenessWitness_mem_cases
    {S_CF : Finset (Package N V × Finset F)}
    {π : Finset (Package N V × Package N V)}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F}
    {g : V → G} {q : Package N_FC V_FC}
    (hq : q ∈ cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g) :
    (∃ n v fs, ((n, v), fs) ∈ S_CF ∧
      q = (hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v)) ∨
    (∃ n v fs f, ((n, v), fs) ∈ S_CF ∧ f ∈ fs ∧
      q = (hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v)) ∨
    (∃ n v m vs fs u, ((n, v), m, vs, fs) ∈ Δ_f ∧ u ∈ vs ∧
      (∃ fs_p, ((n, v), fs_p) ∈ S_CF) ∧
      (∃ fs', fs ⊆ fs' ∧ ((m, u), fs') ∈ S_CF) ∧ ((m, u), (n, v)) ∈ π ∧
      q = (hcfi.cfIntermediateN n v m, hcvr.origV u)) ∨
    (∃ n v f_dep m vs fs u, (((n, v), f_dep), m, vs, fs) ∈ Δ_a ∧ u ∈ vs ∧
      (∃ fs_p, ((n, v), fs_p) ∈ S_CF) ∧
      (∃ fs', fs ⊆ fs' ∧ ((m, u), fs') ∈ S_CF) ∧ ((m, u), (n, v)) ∈ π ∧
      q = (hcfi.cfIntermediateN n v m, hcvr.origV u)) ∨
    (∃ n v m vs fs u f, ((n, v), m, vs, fs) ∈ Δ_f ∧ u ∈ vs ∧ f ∈ fs ∧
      (∃ fs_p, ((n, v), fs_p) ∈ S_CF) ∧
      (∃ fs', fs ⊆ fs' ∧ ((m, u), fs') ∈ S_CF) ∧ ((m, u), (n, v)) ∈ π ∧
      q = (hcfi.cfIntermediateN_f n v m f, hcvr.origV u)) ∨
    (∃ n v f_dep m vs fs u f', (((n, v), f_dep), m, vs, fs) ∈ Δ_a ∧
      u ∈ vs ∧ f' ∈ fs ∧
      (∃ fs_p, ((n, v), fs_p) ∈ S_CF) ∧
      (∃ fs', fs ⊆ fs' ∧ ((m, u), fs') ∈ S_CF) ∧ ((m, u), (n, v)) ∈ π ∧
      q = (hcfi.cfIntermediateN_a n v f_dep m f', hcvr.origV u)) := by
  rw [cfCompletenessWitness] at hq
  rcases Finset.mem_union.mp hq with hq | hq
  rcases Finset.mem_union.mp hq with hq | hq
  rcases Finset.mem_union.mp hq with hq | hq
  rcases Finset.mem_union.mp hq with hq | hq
  rcases Finset.mem_union.mp hq with hq | hq
  · left
    simp only [Finset.mem_image] at hq
    obtain ⟨⟨⟨n, v⟩, fs⟩, hmem, rfl⟩ := hq
    exact ⟨n, v, fs, hmem, rfl⟩
  · right; left
    simp only [Finset.mem_biUnion, Finset.mem_image] at hq
    obtain ⟨⟨⟨n, v⟩, fs⟩, hmem, f, hf, rfl⟩ := hq
    exact ⟨n, v, fs, f, hmem, hf, rfl⟩
  · right; right; left
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hq
    obtain ⟨⟨⟨n, v⟩, m, vs, fs⟩, hdep, u, ⟨hv, hp_S, hscf, hπ⟩, rfl⟩ := hq
    exact ⟨n, v, m, vs, fs, u, hdep, hv, hp_S, hscf, hπ, rfl⟩
  · right; right; right; left
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hq
    obtain ⟨⟨⟨⟨n, v⟩, f_dep⟩, m, vs, fs⟩, hdep, u, ⟨hv, hp_S, hscf, hπ⟩, rfl⟩ := hq
    exact ⟨n, v, f_dep, m, vs, fs, u, hdep, hv, hp_S, hscf, hπ, rfl⟩
  · right; right; right; right; left
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hq
    obtain ⟨⟨⟨n, v⟩, m, vs, fs⟩, hdep, f, hf, u, ⟨hv, hp_S, hscf, hπ⟩, rfl⟩ := hq
    exact ⟨n, v, m, vs, fs, u, f, hdep, hv, hf, hp_S, hscf, hπ, rfl⟩
  · right; right; right; right; right
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hq
    obtain ⟨⟨⟨⟨n, v⟩, f_dep⟩, m, vs, fs⟩, hdep, f', hf', u, ⟨hv, hp_S, hscf, hπ⟩, rfl⟩ := hq
    exact ⟨n, v, f_dep, m, vs, fs, u, f', hdep, hv, hf', hp_S, hscf, hπ, rfl⟩

theorem cfCompletenessWitness_base_mem
    {S_CF : Finset (Package N V × Finset F)}
    {π : Finset (Package N V × Package N V)}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F}
    {g : V → G} {n : N} {v : V} {fs : Finset F}
    (h : ((n, v), fs) ∈ S_CF) :
    (hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v) ∈
      cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g := by
  mem_unions Finset.mem_image.mpr ⟨⟨(n, v), fs⟩, h, rfl⟩

theorem cfCompletenessWitness_feat_mem
    {S_CF : Finset (Package N V × Finset F)}
    {π : Finset (Package N V × Package N V)}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F}
    {g : V → G} {n : N} {v : V} {fs : Finset F} {f : F}
    (h : ((n, v), fs) ∈ S_CF) (hf : f ∈ fs) :
    (hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v) ∈
      cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨(n, v), fs⟩, h, Finset.mem_image.mpr ⟨f, hf, rfl⟩⟩

theorem cfCompletenessWitness_inter_mem_f
    {S_CF : Finset (Package N V × Finset F)}
    {π : Finset (Package N V × Package N V)}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F}
    {g : V → G} {n : N} {v : V} {m : N} {vs : Finset V} {fs : Finset F} {u : V}
    (hdep : ((n, v), m, vs, fs) ∈ Δ_f) (hv : u ∈ vs)
    (hp_S : ∃ fs_p, ((n, v), fs_p) ∈ S_CF)
    (hscf : ∃ fs', fs ⊆ fs' ∧ ((m, u), fs') ∈ S_CF) (hπ : ((m, u), (n, v)) ∈ π) :
    (hcfi.cfIntermediateN n v m, hcvr.origV u) ∈
      cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨(n, v), m, vs, fs⟩, hdep,
    Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hv, hp_S, hscf, hπ⟩, rfl⟩⟩

theorem cfCompletenessWitness_inter_mem_a
    {S_CF : Finset (Package N V × Finset F)}
    {π : Finset (Package N V × Package N V)}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F}
    {g : V → G} {n : N} {v : V} {f_dep : F} {m : N} {vs : Finset V} {fs : Finset F} {u : V}
    (hdep : (((n, v), f_dep), m, vs, fs) ∈ Δ_a) (hv : u ∈ vs)
    (hp_S : ∃ fs_p, ((n, v), fs_p) ∈ S_CF)
    (hscf : ∃ fs', fs ⊆ fs' ∧ ((m, u), fs') ∈ S_CF) (hπ : ((m, u), (n, v)) ∈ π) :
    (hcfi.cfIntermediateN n v m, hcvr.origV u) ∈
      cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨((n, v), f_dep), m, vs, fs⟩, hdep,
    Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hv, hp_S, hscf, hπ⟩, rfl⟩⟩

theorem cfCompletenessWitness_inter_mem_f_feat
    {S_CF : Finset (Package N V × Finset F)}
    {π : Finset (Package N V × Package N V)}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F}
    {g : V → G} {n : N} {v : V} {m : N} {vs : Finset V} {fs : Finset F}
    {u : V} {f : F}
    (hdep : ((n, v), m, vs, fs) ∈ Δ_f) (hv : u ∈ vs) (hf : f ∈ fs)
    (hp_S : ∃ fs_p, ((n, v), fs_p) ∈ S_CF)
    (hscf : ∃ fs', fs ⊆ fs' ∧ ((m, u), fs') ∈ S_CF) (hπ : ((m, u), (n, v)) ∈ π) :
    (hcfi.cfIntermediateN_f n v m f, hcvr.origV u) ∈
      cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨(n, v), m, vs, fs⟩, hdep,
    Finset.mem_biUnion.mpr ⟨f, hf,
      Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hv, hp_S, hscf, hπ⟩, rfl⟩⟩⟩

theorem cfCompletenessWitness_inter_mem_a_feat
    {S_CF : Finset (Package N V × Finset F)}
    {π : Finset (Package N V × Package N V)}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F}
    {g : V → G} {n : N} {v : V} {f_dep : F} {m : N} {vs : Finset V}
    {fs : Finset F} {u : V} {f' : F}
    (hdep : (((n, v), f_dep), m, vs, fs) ∈ Δ_a) (hv : u ∈ vs) (hf' : f' ∈ fs)
    (hp_S : ∃ fs_p, ((n, v), fs_p) ∈ S_CF)
    (hscf : ∃ fs', fs ⊆ fs' ∧ ((m, u), fs') ∈ S_CF) (hπ : ((m, u), (n, v)) ∈ π) :
    (hcfi.cfIntermediateN_a n v f_dep m f', hcvr.origV u) ∈
      cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨((n, v), f_dep), m, vs, fs⟩, hdep,
    Finset.mem_biUnion.mpr ⟨f', hf',
      Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hv, hp_S, hscf, hπ⟩, rfl⟩⟩⟩

/-! ### Completeness Field Lemmas -/

section CompletenessFields

variable (R : Real N V) (Δ_f : Feature.FeatDepRel N V F) (Δ_a : Feature.AddlDepRel N V F)
  (support : Feature.Support N V F) (g : V → G) (r : Package N V)
  (S_CF : Finset (Package N V × Finset F))
  (π : Finset (Package N V × Package N V))
  (hres : IsConcurrentFeatureResolution R support Δ_f Δ_a g r S_CF π)

include hres

theorem cfComplete_subset :
    cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g ⊆
    concurrentFeatureReal R support Δ_f Δ_a g := by
  intro q hq
  rcases cfCompletenessWitness_mem_cases hq with
    ⟨n, v, fs, h, rfl⟩
    | ⟨n, v, fs, f, h, hf, rfl⟩
    | ⟨n, v, m, vs, fs, u, hdep, hv, _, _, _, rfl⟩
    | ⟨n, v, f_dep, m, vs, fs, u, hdep, hv, _, _, _, rfl⟩
    | ⟨n, v, m, vs, fs, u, f, hdep, hv, hf, _, _, _, rfl⟩
    | ⟨n, v, f_dep, m, vs, fs, u, f, hdep, hv, hf, _, _, _, rfl⟩
  · -- Part 1: base orig granular
    have h_orig : (Feature.FeatureName.orig n, v) ∈ Feature.featureReal R support := by
      have := hres.subset (n, v) fs h
      simp_all +decide [Feature.featureReal]
      exact Or.inl (Finset.mem_image.mpr ⟨(n, v), this, rfl⟩)
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (by simpa using h_orig)))))
  · -- Part 2: feature granular
    have h_support : ((n, v), f) ∈ support := hres.support_mem _ _ _ _ h hf
    have h_R : (n, v) ∈ R := hres.subset _ _ h
    have h_feat : (Feature.FeatureName.featured n f, v) ∈ Feature.featureReal R support := by
      simp only [Feature.featureReal, Finset.mem_union]
      right
      exact Finset.mem_biUnion.mpr ⟨((n, v), f), h_support, by
        simp only [if_pos h_R, Finset.mem_singleton]
        rfl⟩
    mem_unions Finset.mem_image.mpr ⟨(Feature.FeatureName.featured n f, v), h_feat, rfl⟩
  · -- Part 3: shared intermediate from Δ_f
    exact mem_cfReal_inter_f hdep hv
  · -- Part 3b: shared intermediate from Δ_a
    exact mem_cfReal_inter_a hdep hv
  · -- Part 4: secondary intermediate from Δ_f
    exact mem_cfReal_inter_f_feat hdep hv hf
  · -- Part 5: secondary intermediate from Δ_a
    exact mem_cfReal_inter_a_feat hdep hv hf

theorem cfComplete_root_mem :
    Concurrent.embedPkg g (Feature.embedPkg F r) ∈
    cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g := by
      exact cfCompletenessWitness_base_mem ( hres.root_mem )

private theorem cfComplete_vu_intermediate
    {pn : N} {pv : V} {m : N} {w1 w2 : V}
    (hπ1 : ((m, w1), (pn, pv)) ∈ π)
    (hπ2 : ((m, w2), (pn, pv)) ∈ π) :
    hcvr.origV w1 = hcvr.origV w2 :=
  congrArg _ (hres.π_functional m w1 w2 (pn, pv) hπ1 hπ2)

set_option maxHeartbeats 3200000 in
private theorem cfComplete_dep_closure_aux
    (p : Package N_FC V_FC)
    (hp : p ∈ cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g)
    (m_fc : N_FC) (vs : Finset V_FC)
    (hdep : (p, m_fc, vs) ∈ concurrentFeatureDeps R support Δ_f Δ_a g) :
    ∃ u ∈ vs, (m_fc, u) ∈ cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g := by
  rcases concurrentFeatureDeps_mem_cases hdep with
    ⟨n, v, f, _, _, hp_eq, hm_eq, hvs_eq⟩
    | ⟨n, v, m, vs_raw, fs, hdep_f, hp_eq, hm_eq, hvs_eq⟩
    | ⟨n, v, m, vs_raw, fs, u, hdep_f, hv_raw, hp_eq, hm_eq, hvs_eq⟩
    | ⟨n, v, m, vs_raw, fs, f, hdep_f, hf_fs, hp_eq, hm_eq, hvs_eq⟩
    | ⟨n, v, m, vs_raw, fs, u, f, hdep_f, hv_raw, hf_fs, hp_eq, hm_eq, hvs_eq⟩
    | ⟨n, v, m, vs_raw, fs, u, f, hdep_f, hu_raw, hf_fs, hp_eq, hm_eq, hvs_eq⟩
    | ⟨n, v, f_dep, m, vs_raw, fs, hdep_a, hp_eq, hm_eq, hvs_eq⟩
    | ⟨n, v, f_dep, m, vs_raw, fs, u, hdep_a, hv_raw, hp_eq, hm_eq, hvs_eq⟩
    | ⟨n, v, f_dep, m, vs_raw, fs, f', hdep_a, hf'_fs, hp_eq, hm_eq, hvs_eq⟩
    | ⟨n, v, f_dep, m, vs_raw, fs, u, f', hdep_a, hv_raw, hf'_fs, hp_eq, hm_eq, hvs_eq⟩
    | ⟨n, v, f_dep, m, vs_raw, fs, u, f', hdep_a, hu_raw, hf'_fs, hp_eq, hm_eq, hvs_eq⟩
  -- supp_back: p = featured granular, m_fc = orig granular, vs = {origV v}.
  · subst hp_eq; subst hm_eq; subst hvs_eq
    rcases cfCompletenessWitness_mem_cases hp with
      ⟨_, _, _, _, hp_eq⟩
      | ⟨n', v', fs', f', hS', _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
    · cf_clash hp_eq
    · simp only [Prod.mk.injEq] at hp_eq
      obtain ⟨hgran, hver⟩ := hp_eq
      obtain ⟨hfn_eq, _⟩ := hcnm.granularN_injective hgran
      have hpair := Feature.FeatureName.featured.inj hfn_eq
      have hv_eq : v = v' := hcvr.origV.injective hver
      refine ⟨hcvr.origV v, ?_, ?_⟩
      · exact Finset.mem_map.mpr ⟨v, Finset.mem_singleton.mpr rfl, rfl⟩
      · have hS'' : ((n, v), fs') ∈ S_CF := by rw [hpair.1, hv_eq]; exact hS'
        exact cfCompletenessWitness_base_mem hS''
    all_goals cf_clash hp_eq
  -- f_depToInter: p = depender's orig granular, m_fc = shared intermediate.
  · subst hp_eq; subst hm_eq; subst hvs_eq
    rcases cfCompletenessWitness_mem_cases hp with
      ⟨n', v', fs', hS', hp_eq⟩
      | ⟨_, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
    · simp only [Prod.mk.injEq] at hp_eq
      obtain ⟨hgran, hver⟩ := hp_eq
      obtain ⟨hfn_eq, _⟩ := hcnm.granularN_injective hgran
      have hn : n = n' := Feature.FeatureName.orig.inj hfn_eq
      have hv_eq : v = v' := hcvr.origV.injective hver
      have hS'' : ((n, v), fs') ∈ S_CF := by rw [hn, hv_eq]; exact hS'
      have hpc := hres.parent_closure (n, v) fs' hS'' m vs_raw fs hdep_f
      obtain ⟨u, ⟨hu_vs, hu_scf, hu_π⟩, _⟩ := hpc
      refine ⟨hcvr.origV u, ?_, ?_⟩
      · exact Finset.mem_map.mpr ⟨u, hu_vs, rfl⟩
      · exact cfCompletenessWitness_inter_mem_f hdep_f hu_vs ⟨fs', hS''⟩ hu_scf hu_π
    · cf_clash hp_eq
    all_goals cf_clash hp_eq
  -- f_interToOrig: p = shared intermediate, m_fc = orig granular.
  · subst hp_eq; subst hm_eq; subst hvs_eq
    rcases cfCompletenessWitness_mem_cases hp with
      ⟨_, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, hp_eq⟩
      | ⟨n', v', m', _, _, u', _, _, _, hscf', _, hp_eq⟩
      | ⟨n', v', _, m', _, _, u', _, _, _, hscf', _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
    all_goals first
      | cf_clash hp_eq
      | (simp only [Prod.mk.injEq] at hp_eq
         obtain ⟨hci, hver⟩ := hp_eq
         have hinj := hcfi.cfIntermediateN_injective _ _ _ _ _ _ hci
         have hv_eq : u = u' := hcvr.origV.injective hver
         obtain ⟨fs'', _, hScf⟩ := hscf'
         have hScf' : ((m, u), fs'') ∈ S_CF := by rw [hinj.2.2, hv_eq]; exact hScf
         refine ⟨hcvr.origV u, ?_, ?_⟩
         · exact Finset.mem_map.mpr ⟨u, Finset.mem_singleton.mpr rfl, rfl⟩
         · exact cfCompletenessWitness_base_mem hScf')
  -- f_depToInterFeat: p = depender's orig, m_fc = secondary cfIntermediateN_f.
  · subst hp_eq; subst hm_eq; subst hvs_eq
    rcases cfCompletenessWitness_mem_cases hp with
      ⟨n', v', fs', hS', hp_eq⟩
      | ⟨_, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
    · simp only [Prod.mk.injEq] at hp_eq
      obtain ⟨hgran, hver⟩ := hp_eq
      obtain ⟨hfn_eq, _⟩ := hcnm.granularN_injective hgran
      have hn : n = n' := Feature.FeatureName.orig.inj hfn_eq
      have hv_eq : v = v' := hcvr.origV.injective hver
      have hS'' : ((n, v), fs') ∈ S_CF := by rw [hn, hv_eq]; exact hS'
      have hpc := hres.parent_closure (n, v) fs' hS'' m vs_raw fs hdep_f
      obtain ⟨u, ⟨hu_vs, hu_scf, hu_π⟩, _⟩ := hpc
      refine ⟨hcvr.origV u, ?_, ?_⟩
      · exact Finset.mem_map.mpr ⟨u, hu_vs, rfl⟩
      · exact cfCompletenessWitness_inter_mem_f_feat hdep_f hu_vs hf_fs
          ⟨fs', hS''⟩ hu_scf hu_π
    · cf_clash hp_eq
    all_goals cf_clash hp_eq
  -- f_interToFeat: p = secondary cfIntermediateN_f at u, m_fc = feature granular at g u.
  · subst hp_eq; subst hm_eq; subst hvs_eq
    rcases cfCompletenessWitness_mem_cases hp with
      ⟨_, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨n', v', m', vs_w, fs_w, u', f_w, hdep_w, hv_w_vs, hf_w, hp_S, hscf', hπ', hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
    all_goals first
      | cf_clash hp_eq
      | (-- Witness intermediate_f_feat. Match args.
         simp only [Prod.mk.injEq] at hp_eq
         obtain ⟨hci, hver⟩ := hp_eq
         have hinj := hcfi.cfIntermediateN_f_injective _ _ _ _ _ _ _ _ hci
         have hv_eq : u = u' := hcvr.origV.injective hver
         have hf_eq : f = f_w := hinj.2.2.2
         have hn_eq : m = m' := hinj.2.2.1
         obtain ⟨fs'', hsub'', hScf⟩ := hscf'
         have hScf' : ((m, u), fs'') ∈ S_CF := by rw [hn_eq, hv_eq]; exact hScf
         have hf_in : f ∈ fs'' := by rw [hf_eq]; exact hsub'' hf_w
         refine ⟨hcvr.origV u, ?_, ?_⟩
         · exact Finset.mem_map.mpr ⟨u, Finset.mem_singleton.mpr rfl, rfl⟩
         · exact cfCompletenessWitness_feat_mem hScf' hf_in)
  -- f_interFeatToInter: p = secondary cfIntermediateN_f at u,
  -- m_fc = shared cfIntermediateN n v m, vs = {origV u}.
  · subst hp_eq; subst hm_eq; subst hvs_eq
    rcases cfCompletenessWitness_mem_cases hp with
      ⟨_, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨n', v', m', vs_w, fs_w, u', f_w, hdep_w, hv_w_vs, hf_w, hp_S, hscf', hπ', hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
    all_goals first
      | cf_clash hp_eq
      | (-- Witness case 5: secondary cfIntermediateN_f at u' from entry (vs_w, fs_w).
         -- Place the shared cfIntermediateN at u in Part 3 using the SAME entry (vs_w, fs_w);
         -- the Part 3 filter conditions are identical to the Part 4 filter conditions.
         simp only [Prod.mk.injEq] at hp_eq
         obtain ⟨hci, hver⟩ := hp_eq
         have hinj := hcfi.cfIntermediateN_f_injective _ _ _ _ _ _ _ _ hci
         have hu_eq : u = u' := hcvr.origV.injective hver
         have hpn_eq : n = n' := hinj.1
         have hpv_eq : v = v' := hinj.2.1
         have hn_eq : m = m' := hinj.2.2.1
         subst hpn_eq; subst hpv_eq; subst hn_eq; subst hu_eq
         refine ⟨hcvr.origV u, ?_, ?_⟩
         · exact Finset.mem_map.mpr ⟨u, Finset.mem_singleton.mpr rfl, rfl⟩
         · exact cfCompletenessWitness_inter_mem_f hdep_w hv_w_vs hp_S hscf' hπ')
  -- a_depToInter: p = depender's featured granular, m_fc = shared intermediate.
  · subst hp_eq; subst hm_eq; subst hvs_eq
    rcases cfCompletenessWitness_mem_cases hp with
      ⟨_, _, _, _, hp_eq⟩
      | ⟨n', v', fs', f', hS', hf', hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
    · cf_clash hp_eq
    · simp only [Prod.mk.injEq] at hp_eq
      obtain ⟨hgran, hver⟩ := hp_eq
      obtain ⟨hfn_eq, _⟩ := hcnm.granularN_injective hgran
      have hpair := Feature.FeatureName.featured.inj hfn_eq
      have hv_eq : v = v' := hcvr.origV.injective hver
      have hS'' : ((n, v), fs') ∈ S_CF := by rw [hpair.1, hv_eq]; exact hS'
      have hf_in : f_dep ∈ fs' := by rw [hpair.2]; exact hf'
      have hpc := hres.parent_closure_addl (n, v) fs' hS'' f_dep hf_in m vs_raw fs hdep_a
      obtain ⟨u, ⟨hu_vs, hu_scf, hu_π⟩, _⟩ := hpc
      refine ⟨hcvr.origV u, ?_, ?_⟩
      · exact Finset.mem_map.mpr ⟨u, hu_vs, rfl⟩
      · exact cfCompletenessWitness_inter_mem_a hdep_a hu_vs ⟨fs', hS''⟩ hu_scf hu_π
    all_goals cf_clash hp_eq
  -- a_interToOrig: p = shared intermediate, m_fc = orig granular.
  · subst hp_eq; subst hm_eq; subst hvs_eq
    rcases cfCompletenessWitness_mem_cases hp with
      ⟨_, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, hp_eq⟩
      | ⟨n', v', m', _, _, u', _, _, _, hscf', _, hp_eq⟩
      | ⟨n', v', _, m', _, _, u', _, _, _, hscf', _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
    all_goals first
      | cf_clash hp_eq
      | (simp only [Prod.mk.injEq] at hp_eq
         obtain ⟨hci, hver⟩ := hp_eq
         have hinj := hcfi.cfIntermediateN_injective _ _ _ _ _ _ hci
         have hv_eq : u = u' := hcvr.origV.injective hver
         obtain ⟨fs'', _, hScf⟩ := hscf'
         have hScf' : ((m, u), fs'') ∈ S_CF := by rw [hinj.2.2, hv_eq]; exact hScf
         refine ⟨hcvr.origV u, ?_, ?_⟩
         · exact Finset.mem_map.mpr ⟨u, Finset.mem_singleton.mpr rfl, rfl⟩
         · exact cfCompletenessWitness_base_mem hScf')
  -- a_depToInterFeat: p = depender's featured granular, m_fc = secondary cfIntermediateN_a.
  · subst hp_eq; subst hm_eq; subst hvs_eq
    rcases cfCompletenessWitness_mem_cases hp with
      ⟨_, _, _, _, hp_eq⟩
      | ⟨n', v', fs', f', hS', hf', hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
    · cf_clash hp_eq
    · simp only [Prod.mk.injEq] at hp_eq
      obtain ⟨hgran, hver⟩ := hp_eq
      obtain ⟨hfn_eq, _⟩ := hcnm.granularN_injective hgran
      have hpair := Feature.FeatureName.featured.inj hfn_eq
      have hv_eq : v = v' := hcvr.origV.injective hver
      have hS'' : ((n, v), fs') ∈ S_CF := by rw [hpair.1, hv_eq]; exact hS'
      have hf_in : f_dep ∈ fs' := by rw [hpair.2]; exact hf'
      have hpc := hres.parent_closure_addl (n, v) fs' hS'' f_dep hf_in m vs_raw fs hdep_a
      obtain ⟨u, ⟨hu_vs, hu_scf, hu_π⟩, _⟩ := hpc
      refine ⟨hcvr.origV u, ?_, ?_⟩
      · exact Finset.mem_map.mpr ⟨u, hu_vs, rfl⟩
      · exact cfCompletenessWitness_inter_mem_a_feat hdep_a hu_vs hf'_fs
          ⟨fs', hS''⟩ hu_scf hu_π
    all_goals cf_clash hp_eq
  -- a_interToFeat: p = secondary cfIntermediateN_a at u, m_fc = feature granular at g u.
  · subst hp_eq; subst hm_eq; subst hvs_eq
    rcases cfCompletenessWitness_mem_cases hp with
      ⟨_, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨n', v', f_dep', m', vs_w, fs_w, u', f_w, hdep_w, hv_w_vs, hf_w, hp_S, hscf', hπ', hp_eq⟩
    all_goals first
      | cf_clash hp_eq
      | (simp only [Prod.mk.injEq] at hp_eq
         obtain ⟨hci, hver⟩ := hp_eq
         have hinj := hcfi.cfIntermediateN_a_injective _ _ _ _ _ _ _ _ _ _ hci
         have hv_eq : u = u' := hcvr.origV.injective hver
         have hf_eq : f' = f_w := hinj.2.2.2.2
         have hn_eq : m = m' := hinj.2.2.2.1
         obtain ⟨fs'', hsub'', hScf⟩ := hscf'
         have hScf' : ((m, u), fs'') ∈ S_CF := by rw [hn_eq, hv_eq]; exact hScf
         have hf_in : f' ∈ fs'' := by rw [hf_eq]; exact hsub'' hf_w
         refine ⟨hcvr.origV u, ?_, ?_⟩
         · exact Finset.mem_map.mpr ⟨u, Finset.mem_singleton.mpr rfl, rfl⟩
         · exact cfCompletenessWitness_feat_mem hScf' hf_in)
  -- a_interFeatToInter: p = secondary cfIntermediateN_a at u,
  -- m_fc = shared cfIntermediateN n v m, vs = {origV u}.
  · subst hp_eq; subst hm_eq; subst hvs_eq
    rcases cfCompletenessWitness_mem_cases hp with
      ⟨_, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hp_eq⟩
      | ⟨n', v', f_dep', m', vs_w, fs_w, u', f_w, hdep_w, hv_w_vs, hf_w, hp_S, hscf', hπ', hp_eq⟩
    all_goals first
      | cf_clash hp_eq
      | (-- Witness case 6: secondary cfIntermediateN_a at u' from entry (vs_w, fs_w).
         -- Place the shared cfIntermediateN at u in Part 3b using the SAME entry; the Part 3b
         -- filter conditions are identical to the Part 5 filter conditions.
         simp only [Prod.mk.injEq] at hp_eq
         obtain ⟨hci, hver⟩ := hp_eq
         have hinj := hcfi.cfIntermediateN_a_injective _ _ _ _ _ _ _ _ _ _ hci
         have hu_eq : u = u' := hcvr.origV.injective hver
         have hpn_eq : n = n' := hinj.1
         have hpv_eq : v = v' := hinj.2.1
         have hfd_eq : f_dep = f_dep' := hinj.2.2.1
         have hn_eq : m = m' := hinj.2.2.2.1
         subst hpn_eq; subst hpv_eq; subst hn_eq; subst hu_eq; subst hfd_eq
         refine ⟨hcvr.origV u, ?_, ?_⟩
         · exact Finset.mem_map.mpr ⟨u, Finset.mem_singleton.mpr rfl, rfl⟩
         · exact cfCompletenessWitness_inter_mem_a hdep_w hv_w_vs hp_S hscf' hπ')

theorem cfComplete_dep_closure :
    ∀ p ∈ cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g,
    ∀ m vs, (p, m, vs) ∈ concurrentFeatureDeps R support Δ_f Δ_a g →
    ∃ v ∈ vs, (m, v) ∈ cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g :=
  fun p hp m vs hdep => cfComplete_dep_closure_aux R Δ_f Δ_a support g r S_CF π hres p hp m vs hdep

-- Helper: same granular name, same g value, use version_granularity
private theorem cfComplete_vu_granular_same
    {n : N} {w1 w2 : V} {fs1 fs2 : Finset F}
    (hS1 : ((n, w1), fs1) ∈ S_CF) (hS2 : ((n, w2), fs2) ∈ S_CF)
    (hg : g w1 = g w2) : hcvr.origV w1 = hcvr.origV w2 := by
  by_contra h_ne
  have hv_ne : w1 ≠ w2 := fun h => h_ne (congrArg hcvr.origV h)
  exact absurd hg (hres.version_granularity n w1 w2 fs1 fs2 hS1 hS2 hv_ne)

set_option maxHeartbeats 6400000 in
theorem cfComplete_version_unique :
    VersionUnique (cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g) := by
  intro nm cv₁ cv₂ h₁ h₂
  rcases cfCompletenessWitness_mem_cases h₁ with
    ⟨n₁, v₁, fs₁, hS₁, heq₁⟩
    | ⟨n₁, v₁, fs₁, f₁, hS₁, _, heq₁⟩
    | ⟨n₁, v₁, m₁, vs_w₁, fs_w₁, u₁, hdep_w₁, hv_w_vs₁, hp_S₁, hscf₁, hπ₁, heq₁⟩
    | ⟨n₁, v₁, fd_w₁, m₁, vs_w₁, fs_w₁, u₁, hdep_w₁, hv_w_vs₁, hp_S₁, hscf₁, hπ₁, heq₁⟩
    | ⟨n₁, v₁, m₁, vs_w₁, fs_w₁, u₁, f_w₁, hdep_w₁, hv_w_vs₁, hf_w₁, hp_S₁, hscf₁, hπ₁, heq₁⟩
    | ⟨n₁, v₁, fd_w₁, m₁, vs_w₁, fs_w₁, u₁, f_w₁, hdep_w₁, hv_w_vs₁, hf_w₁, hp_S₁, hscf₁, hπ₁, heq₁⟩ <;>
  rcases cfCompletenessWitness_mem_cases h₂ with
    ⟨n₂, v₂, fs₂, hS₂, heq₂⟩
    | ⟨n₂, v₂, fs₂, f₂, hS₂, _, heq₂⟩
    | ⟨n₂, v₂, m₂, vs_w₂, fs_w₂, u₂, hdep_w₂, hv_w_vs₂, hp_S₂, hscf₂, hπ₂, heq₂⟩
    | ⟨n₂, v₂, fd_w₂, m₂, vs_w₂, fs_w₂, u₂, hdep_w₂, hv_w_vs₂, hp_S₂, hscf₂, hπ₂, heq₂⟩
    | ⟨n₂, v₂, m₂, vs_w₂, fs_w₂, u₂, f_w₂, hdep_w₂, hv_w_vs₂, hf_w₂, hp_S₂, hscf₂, hπ₂, heq₂⟩
    | ⟨n₂, v₂, fd_w₂, m₂, vs_w₂, fs_w₂, u₂, f_w₂, hdep_w₂, hv_w_vs₂, hf_w₂, hp_S₂, hscf₂, hπ₂, heq₂⟩ <;>
  simp only [Prod.mk.injEq] at heq₁ heq₂ <;>
  obtain ⟨h1n, rfl⟩ := heq₁ <;>
  obtain ⟨h2n, rfl⟩ := heq₂ <;>
  (first
    | (-- granular_orig × granular_orig (must come before featured)
       have ⟨hfn_eq, hg_eq⟩ := hcnm.granularN_injective (h1n.symm.trans h2n)
       have hn_eq : n₁ = n₂ := Feature.FeatureName.orig.inj hfn_eq
       subst hn_eq
       exact cfComplete_vu_granular_same (R := R) (Δ_f := Δ_f) (Δ_a := Δ_a)
         (support := support) (g := g) (r := r) (S_CF := S_CF) (π := π) hres
         hS₁ hS₂ hg_eq)
    | (-- granular_featured × granular_featured
       have ⟨hfn_eq, hg_eq⟩ := hcnm.granularN_injective (h1n.symm.trans h2n)
       have ⟨hn_eq, _⟩ := Feature.FeatureName.featured.inj hfn_eq
       subst hn_eq
       exact cfComplete_vu_granular_same (R := R) (Δ_f := Δ_f) (Δ_a := Δ_a)
         (support := support) (g := g) (r := r) (S_CF := S_CF) (π := π) hres
         hS₁ hS₂ hg_eq)
    | cf_name_clash (h1n.symm.trans h2n)
    | (have hinj := hcfi.cfIntermediateN_injective _ _ _ _ _ _ (h1n.symm.trans h2n)
       obtain ⟨hpn, hpv, hn⟩ := hinj
       subst hpn; subst hpv; subst hn
       apply cfComplete_vu_intermediate (R := R) (Δ_f := Δ_f) (Δ_a := Δ_a) (support := support)
         (g := g) (r := r) (S_CF := S_CF) (π := π) hres hπ₁ hπ₂)
    | (have hinj := hcfi.cfIntermediateN_f_injective _ _ _ _ _ _ _ _ (h1n.symm.trans h2n)
       obtain ⟨hpn, hpv, hn, _⟩ := hinj
       subst hpn; subst hpv; subst hn
       have h_eq : u₁ = u₂ := hres.π_functional _ _ _ _ hπ₁ hπ₂
       subst h_eq; rfl)
    | (have hinj := hcfi.cfIntermediateN_a_injective _ _ _ _ _ _ _ _ _ _ (h1n.symm.trans h2n)
       obtain ⟨hpn, hpv, _, hn, _⟩ := hinj
       subst hpn; subst hpv; subst hn
       have h_eq : u₁ = u₂ := hres.π_functional _ _ _ _ hπ₁ hπ₂
       subst h_eq; rfl))

end CompletenessFields

/-! ### Completeness -/

theorem concurrent_feature_completeness
    (R : Real N V)
    (Δ_f : Feature.FeatDepRel N V F) (Δ_a : Feature.AddlDepRel N V F)
    (support : Feature.Support N V F)
    (g : V → G) (r : Package N V)
    (S_CF : Finset (Package N V × Finset F))
    (π : Finset (Package N V × Package N V))
    (hres : IsConcurrentFeatureResolution R support Δ_f Δ_a g r S_CF π) :
    IsResolution
      (concurrentFeatureReal R support Δ_f Δ_a g)
      (concurrentFeatureDeps R support Δ_f Δ_a g)
      (Concurrent.embedPkg g (Feature.embedPkg F r))
      (cfCompletenessWitness (N_FC := N_FC) (V_FC := V_FC) S_CF π Δ_f Δ_a g) :=
  ⟨cfComplete_subset R Δ_f Δ_a support g r S_CF π hres,
   cfComplete_root_mem R Δ_f Δ_a support g r S_CF π hres,
   cfComplete_dep_closure R Δ_f Δ_a support g r S_CF π hres,
   cfComplete_version_unique R Δ_f Δ_a support g r S_CF π hres⟩

end PackageCalculus.Composition
