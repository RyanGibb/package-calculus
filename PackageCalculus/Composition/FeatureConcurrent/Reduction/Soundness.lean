import PackageCalculus.Composition.FeatureConcurrent.Types
import PackageCalculus.Composition.FeatureConcurrent.Definition
import PackageCalculus.Composition.FeatureConcurrent.Reduction.Definition
import PackageCalculus.Extensions.Feature.Definition
import PackageCalculus.Extensions.Feature.Reduction.Definition
import PackageCalculus.Extensions.Feature.Reduction.Soundness
import PackageCalculus.Extensions.Concurrent.Definition
import PackageCalculus.Extensions.Concurrent.Reduction.Definition
import PackageCalculus.Extensions.Concurrent.Reduction.Soundness
import Mathlib

/-! # Feature-concurrent composition: soundness

Any core resolution of the feature-concurrent encoding projects back to a
valid `IsConcurrentFeatureResolution` of the original problem. -/

namespace PackageCalculus.Composition

open Classical

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {F : Type*} [DecidableEq F] {G : Type*} [DecidableEq G]
variable {N_FC : Type*} [DecidableEq N_FC] {V_FC : Type*} [DecidableEq V_FC]
variable [hcnm : Concurrent.HasConcurrentNames (Feature.FeatureName N F) V G N_FC]
variable [hcvr : Concurrent.HasConcurrentVersions V G V_FC]
variable [hcfi : HasConcurrentFeatureIntermediate N V F G N_FC]

set_option linter.unusedSectionVars false

/-! ### Witness Constructions -/

/-- Combined embedding: maps `(n, v) : Package N V` to the granular origN package. -/
def cfEmbedOrigPkg (g : V → G) (p : Package N V) : Package N_FC V_FC :=
  (hcnm.granularN (@Feature.FeatureName.orig N F p.1) (g p.2), hcvr.origV p.2)

theorem cfEmbedOrigPkg_injective (g : V → G) :
    Function.Injective (cfEmbedOrigPkg (hcnm := hcnm) (hcvr := hcvr) g :
      Package N V → Package N_FC V_FC) := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [cfEmbedOrigPkg, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have ⟨hfn, _⟩ := hcnm.granularN_injective h1
  exact Prod.ext (Feature.FeatureName.orig.inj hfn) (hcvr.origV.injective h2)

/-- Soundness witness `S_CF`. Extracts `((n, v), fs)` entries by collecting orig granular
    packages in `S` and gathering their feature companions. -/
noncomputable def cfSoundnessWitnessS [Fintype F] (g : V → G)
    (S : Finset (Package N_FC V_FC)) : Finset (Package N V × Finset F) :=
  (S.preimage (cfEmbedOrigPkg (F := F) g) (Set.InjOn.mono (Set.subset_univ _)
    (cfEmbedOrigPkg_injective (F := F) g).injOn)).image
    (fun ⟨n, v⟩ =>
      ((n, v), Finset.univ.filter (fun f =>
        (hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v) ∈ S)))

/-- Soundness witness `π`. Extracts `((n, v), (p_n, p_v))` entries from the shared
    intermediate constructor: each cfIntermediate package present in `S` records a single
    parent relationship `((n, v), (p_n, p_v))`. -/
def cfSoundnessWitnessπ
    (Δ_f : Feature.FeatDepRel N V F) (Δ_a : Feature.AddlDepRel N V F)
    (g : V → G) (S : Finset (Package N_FC V_FC)) :
    Finset (Package N V × Package N V) :=
  -- For each Δ_f entry, gather versions v ∈ vs where the shared intermediate witnesses S.
  Δ_f.biUnion (fun ⟨⟨p_n, p_v⟩, n, vs, _⟩ =>
    (vs.filter (fun v =>
      (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v) ∈ S ∧
      (hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v) ∈ S)).image
      (fun v => ((n, v), (p_n, p_v)))) ∪
  Δ_a.biUnion (fun ⟨⟨⟨p_n, p_v⟩, _⟩, n, vs, _⟩ =>
    (vs.filter (fun v =>
      (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v) ∈ S ∧
      (hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v) ∈ S)).image
      (fun v => ((n, v), (p_n, p_v))))

/-! ### Witness Membership Helpers -/

theorem mem_cfSoundnessWitnessS [Fintype F] {g : V → G}
    {S : Finset (Package N_FC V_FC)} {p : Package N V × Finset F}
    (h : p ∈ cfSoundnessWitnessS (N := N) (F := F) g S) :
    ∃ n v, (hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v) ∈ S ∧
      p = ((n, v), Finset.univ.filter (fun f =>
        (hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v) ∈ S)) := by
  simp only [cfSoundnessWitnessS, Finset.mem_image, Finset.mem_preimage, cfEmbedOrigPkg] at h
  obtain ⟨⟨n, v⟩, hmem, rfl⟩ := h
  exact ⟨n, v, hmem, rfl⟩

theorem mem_cfSoundnessWitnessS_of [Fintype F] {g : V → G}
    {S : Finset (Package N_FC V_FC)} {n : N} {v : V}
    (h : (hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v) ∈ S) :
    ((n, v), Finset.univ.filter (fun f =>
      (hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v) ∈ S)) ∈
      cfSoundnessWitnessS (N := N) (F := F) g S := by
  simp only [cfSoundnessWitnessS, Finset.mem_image, Finset.mem_preimage, cfEmbedOrigPkg]
  exact ⟨(n, v), h, rfl⟩

theorem mem_cfSoundnessWitnessπ {Δ_f : Feature.FeatDepRel N V F}
    {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {S : Finset (Package N_FC V_FC)} {pair : Package N V × Package N V}
    (h : pair ∈ cfSoundnessWitnessπ Δ_f Δ_a g S) :
    (∃ p_n p_v n vs fs v, ((p_n, p_v), n, vs, fs) ∈ Δ_f ∧ v ∈ vs ∧
      (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v) ∈ S ∧
      (hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v) ∈ S ∧
      pair = ((n, v), (p_n, p_v))) ∨
    (∃ p_n p_v f n vs fs v, (((p_n, p_v), f), n, vs, fs) ∈ Δ_a ∧ v ∈ vs ∧
      (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v) ∈ S ∧
      (hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v) ∈ S ∧
      pair = ((n, v), (p_n, p_v))) := by
  simp only [cfSoundnessWitnessπ, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter] at h
  rcases h with ⟨⟨⟨p_n, p_v⟩, n, vs, fs⟩, hdep, v, ⟨hv, h1, h2⟩, rfl⟩ |
    ⟨⟨⟨⟨p_n, p_v⟩, f⟩, n, vs, fs⟩, hdep, v, ⟨hv, h1, h2⟩, rfl⟩
  · left; exact ⟨p_n, p_v, n, vs, fs, v, hdep, hv, h1, h2, rfl⟩
  · right; exact ⟨p_n, p_v, f, n, vs, fs, v, hdep, hv, h1, h2, rfl⟩

theorem mem_cfSoundnessWitnessπ_f {Δ_f : Feature.FeatDepRel N V F}
    {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {S : Finset (Package N_FC V_FC)}
    {p_n : N} {p_v : V} {n : N} {vs : Finset V} {fs : Finset F} {v : V}
    (hdep : ((p_n, p_v), n, vs, fs) ∈ Δ_f) (hv : v ∈ vs)
    (h1 : (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v) ∈ S)
    (h2 : (hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v) ∈ S) :
    ((n, v), (p_n, p_v)) ∈ cfSoundnessWitnessπ Δ_f Δ_a g S := by
  simp only [cfSoundnessWitnessπ, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter]
  left
  exact ⟨⟨⟨p_n, p_v⟩, n, vs, fs⟩, hdep, v, ⟨hv, h1, h2⟩, rfl⟩

theorem mem_cfSoundnessWitnessπ_a {Δ_f : Feature.FeatDepRel N V F}
    {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {S : Finset (Package N_FC V_FC)}
    {p_n : N} {p_v : V} {f : F} {n : N} {vs : Finset V} {fs : Finset F} {v : V}
    (hdep : (((p_n, p_v), f), n, vs, fs) ∈ Δ_a) (hv : v ∈ vs)
    (h1 : (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v) ∈ S)
    (h2 : (hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v) ∈ S) :
    ((n, v), (p_n, p_v)) ∈ cfSoundnessWitnessπ Δ_f Δ_a g S := by
  simp only [cfSoundnessWitnessπ, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter]
  right
  exact ⟨⟨⟨⟨p_n, p_v⟩, f⟩, n, vs, fs⟩, hdep, v, ⟨hv, h1, h2⟩, rfl⟩

/-- Every π edge puts the corresponding shared intermediate in `S`. -/
theorem cfSoundnessWitnessπ_inter_mem {Δ_f : Feature.FeatDepRel N V F}
    {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {S : Finset (Package N_FC V_FC)} {n : N} {v : V} {p_n : N} {p_v : V}
    (h : ((n, v), (p_n, p_v)) ∈ cfSoundnessWitnessπ Δ_f Δ_a g S) :
    (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v) ∈ S := by
  rcases mem_cfSoundnessWitnessπ h with
    ⟨p_n', p_v', n', vs, fs, v₀, _, _, h_inter, _, h_eq⟩
    | ⟨p_n', p_v', f, n', vs, fs, v₀, _, _, h_inter, _, h_eq⟩
  all_goals
    simp only [Prod.mk.injEq] at h_eq
    obtain ⟨⟨hn, hv⟩, hpn, hpv⟩ := h_eq
    subst hn; subst hv; subst hpn; subst hpv
    exact h_inter

/-! ### Soundness Field Lemmas -/

section SoundnessFields

variable [Fintype F]
variable (R : Real N V) (support : Feature.Support N V F)
  (Δ_f : Feature.FeatDepRel N V F) (Δ_a : Feature.AddlDepRel N V F)
  (g : V → G) (r : Package N V) (S : Finset (Package N_FC V_FC))
  (hres : IsResolution
    (concurrentFeatureReal R support Δ_f Δ_a g)
    (concurrentFeatureDeps R support Δ_f Δ_a g)
    (Concurrent.embedPkg g (Feature.embedPkg F r)) S)
  (hroot_no_support : ∀ f, (r, f) ∉ support)

include hres hroot_no_support

omit hroot_no_support in
theorem cfSound_subset :
    ∀ p fs, (p, fs) ∈ cfSoundnessWitnessS (N := N) (F := F) g S → p ∈ R := by
      intro p fs hp;
      obtain ⟨ n, v, hnv, hp ⟩ := mem_cfSoundnessWitnessS hp;
      have := hres.1 hnv; simp_all +decide [ concurrentFeatureReal ] ;
      unfold Concurrent.embedReal at this; simp_all +decide [ Concurrent.embedPkg ] ;
      obtain ⟨ a, ha, ha' ⟩ := this; have := hcnm.granularN_injective ha'; simp_all +decide [ Feature.featureReal ] ;
      rcases ha with ( ha | ⟨ a, b, c, ha, hb ⟩ ) <;> simp_all +decide [ Feature.embedSet ] ;
      · obtain ⟨ a, b, hab, h ⟩ := ha; simp_all +decide [ Feature.embedPkg ] ;
        cases h.1 ; aesop ( simp_config := { singlePass := true } ) ;
      · split_ifs at hb <;> simp_all +decide [ Feature.HasFeatureNames.featuredN ]

theorem cfSound_root_mem :
    (r, ∅) ∈ cfSoundnessWitnessS (N := N) (F := F) g S := by
      have h_filter_empty : ∀ f : F, (hcnm.granularN (Feature.FeatureName.featured r.1 f) (g r.2), hcvr.origV r.2) ∉ S := by
        intro f hf
        have h_in_concurrentFeatureReal : (hcnm.granularN (Feature.FeatureName.featured r.1 f) (g r.2), hcvr.origV r.2) ∈ concurrentFeatureReal R support Δ_f Δ_a g := by
          grind +splitIndPred;
        unfold concurrentFeatureReal at h_in_concurrentFeatureReal;
        unfold Concurrent.embedReal at h_in_concurrentFeatureReal;
        simp +decide [ Concurrent.embedPkg, Feature.featureReal ] at h_in_concurrentFeatureReal;
        obtain ⟨ a, ha₁, ha₂ ⟩ := h_in_concurrentFeatureReal;
        rcases ha₁ with ( ha₁ | ⟨ a, b, c, ha₁, ha₂ ⟩ );
        · cases a <;> simp +decide [ hcnm.granularN_injective.eq_iff ] at ha₂ ⊢;
          unfold Feature.embedSet at ha₁; simp +decide [ ha₂ ] at ha₁;
          obtain ⟨ a, b, hab, h ⟩ := ha₁; cases h;
        · split_ifs at ha₂ <;> simp_all +decide [ Feature.HasFeatureNames.featuredN ];
          have := hcnm.granularN_injective; simp_all +decide [ Function.Injective2 ] ;
          specialize this ‹_› ; aesop ( simp_config := { singlePass := true } ) ;
      convert mem_cfSoundnessWitnessS_of _;
      · exact Eq.symm ( Finset.eq_empty_of_forall_notMem fun f hf => h_filter_empty f <| Finset.mem_filter.mp hf |>.2 );
      · convert hres.root_mem using 1

omit hres hroot_no_support in
theorem cfSound_feature_unification :
    ∀ n v fs fs',
    ((n, v), fs) ∈ cfSoundnessWitnessS (N := N) (F := F) g S →
    ((n, v), fs') ∈ cfSoundnessWitnessS (N := N) (F := F) g S → fs = fs' := by
  unfold cfSoundnessWitnessS
  grind

omit hroot_no_support in
theorem cfSound_parent_closure :
    ∀ p fs_p, (p, fs_p) ∈ cfSoundnessWitnessS (N := N) (F := F) g S →
    ∀ n vs fs, (p, n, vs, fs) ∈ Δ_f →
    ∃! v, v ∈ vs ∧
      (∃ fs', fs ⊆ fs' ∧ ((n, v), fs') ∈ cfSoundnessWitnessS (N := N) (F := F) g S) ∧
      ((n, v), p) ∈ cfSoundnessWitnessπ Δ_f Δ_a g S := by
        intro p fs_p hp n vs fs hdep
        obtain ⟨p_n, p_v, h_p, h_pn⟩ :
            ∃ p_n p_v, p = (p_n, p_v) ∧
              (hcnm.granularN (.orig p_n) (g p_v), hcvr.origV p_v) ∈ S := by
          obtain ⟨pn, pv, hpn_S, hp_eq⟩ := mem_cfSoundnessWitnessS hp
          simp only [Prod.mk.injEq] at hp_eq
          exact ⟨pn, pv, hp_eq.1, hpn_S⟩
        subst h_p
        -- By hres.dep_closure on depender's orig → shared intermediate, get v_fc ∈ vs.map origV
        -- with (cfIntermediateN p_n p_v n, v_fc) ∈ S.
        obtain ⟨v_fc, hv_fc_mem, hv_fc_S⟩ :
            ∃ v_fc ∈ vs.map hcvr.origV,
              (hcfi.cfIntermediateN p_n p_v n, v_fc) ∈ S :=
          hres.dep_closure _ h_pn _ _ (mem_cfDeps_f_depToInter hdep)
        obtain ⟨v₀, hv₀_vs, rfl⟩ := Finset.mem_map.mp hv_fc_mem
        -- Also need (granularN orig n (g v₀), origV v₀) ∈ S via intermediate→orig dep_closure.
        have h_orig_S : (hcnm.granularN (Feature.FeatureName.orig n) (g v₀), hcvr.origV v₀) ∈ S := by
          simpa using hres.dep_closure _ hv_fc_S _ _ (mem_cfDeps_f_interToOrig hdep hv₀_vs)
        refine ⟨v₀, ⟨hv₀_vs, ⟨_, ?_, mem_cfSoundnessWitnessS_of h_orig_S⟩,
          mem_cfSoundnessWitnessπ_f hdep hv₀_vs hv_fc_S h_orig_S⟩, ?_⟩
        · -- fs ⊆ filter showing each f ∈ fs has its feature granular in S at version v₀.
          intro f hf
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          -- depender → secondary: get the secondary at some v_f ∈ vs.
          obtain ⟨v_f_fc, hv_f_mem, hv_f_S⟩ :=
            hres.dep_closure _ h_pn _ _ (mem_cfDeps_f_depToInterFeat hdep hf)
          obtain ⟨v_f, hv_f_vs, rfl⟩ := Finset.mem_map.mp hv_f_mem
          -- back-edge: secondary at v_f → shared at v_f.
          have hshared_v_f_S : (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v_f) ∈ S := by
            simpa using hres.dep_closure _ hv_f_S _ _ (mem_cfDeps_f_interFeatToInter hdep hv_f_vs hf)
          -- version_unique on shared intermediate: shared at v_f = shared at v₀.
          have hver : hcvr.origV v_f = hcvr.origV v₀ :=
            hres.version_unique _ _ _ hshared_v_f_S hv_fc_S
          have hv_eq : v_f = v₀ := hcvr.origV.injective hver
          subst hv_eq
          -- secondary at v₀ → feature granular at v₀.
          simpa using hres.dep_closure _ hv_f_S _ _ (mem_cfDeps_f_interToFeat hdep hv_f_vs hf)
        · -- Uniqueness
          rintro y ⟨hy_vs, _, hπ⟩
          exact hcvr.origV.injective (hres.version_unique _ _ _
            (cfSoundnessWitnessπ_inter_mem hπ) hv_fc_S)

omit hroot_no_support in
theorem cfSound_parent_closure_addl :
    ∀ p fs_p, (p, fs_p) ∈ cfSoundnessWitnessS (N := N) (F := F) g S →
    ∀ f ∈ fs_p, ∀ n vs fs, ((p, f), n, vs, fs) ∈ Δ_a →
    ∃! v, v ∈ vs ∧
      (∃ fs', fs ⊆ fs' ∧ ((n, v), fs') ∈ cfSoundnessWitnessS (N := N) (F := F) g S) ∧
      ((n, v), p) ∈ cfSoundnessWitnessπ Δ_f Δ_a g S := by
        intro p fs_p hp f hf n vs fs hdep
        -- Extract p = (p_n, p_v) along with both orig and featured packages in S.
        obtain ⟨p_n, p_v, h_p, h_orig_pn, h_feat_pn⟩ :
            ∃ p_n p_v, p = (p_n, p_v) ∧
              (hcnm.granularN (Feature.FeatureName.orig p_n) (g p_v), hcvr.origV p_v) ∈ S ∧
              (hcnm.granularN (Feature.FeatureName.featured p_n f) (g p_v), hcvr.origV p_v) ∈ S := by
          obtain ⟨pn, pv, hpn_S, hp_eq⟩ := mem_cfSoundnessWitnessS hp
          simp only [Prod.mk.injEq] at hp_eq
          have h_f_filter : f ∈ Finset.univ.filter
              (fun f' => (hcnm.granularN (Feature.FeatureName.featured pn f') (g pv),
                hcvr.origV pv) ∈ S) := by rw [← hp_eq.2]; exact hf
          have h_feat := (Finset.mem_filter.mp h_f_filter).2
          exact ⟨pn, pv, hp_eq.1, hpn_S, h_feat⟩
        subst h_p
        -- By hres.dep_closure on featured depender → shared intermediate, get v₀.
        obtain ⟨v_fc, hv_fc_mem, hv_fc_S⟩ :
            ∃ v_fc ∈ vs.map hcvr.origV,
              (hcfi.cfIntermediateN p_n p_v n, v_fc) ∈ S :=
          hres.dep_closure _ h_feat_pn _ _ (mem_cfDeps_a_depToInter hdep)
        obtain ⟨v₀, hv₀_vs, rfl⟩ := Finset.mem_map.mp hv_fc_mem
        have h_orig_S : (hcnm.granularN (Feature.FeatureName.orig n) (g v₀), hcvr.origV v₀) ∈ S := by
          simpa using hres.dep_closure _ hv_fc_S _ _ (mem_cfDeps_a_interToOrig hdep hv₀_vs)
        refine ⟨v₀, ⟨hv₀_vs, ⟨_, ?_, mem_cfSoundnessWitnessS_of h_orig_S⟩,
          mem_cfSoundnessWitnessπ_a hdep hv₀_vs hv_fc_S h_orig_S⟩, ?_⟩
        · -- fs ⊆ filter showing each f' ∈ fs has its feature granular in S at version v₀.
          intro f' hf'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          -- depender (featured) → secondary: get the secondary at some v_f ∈ vs.
          obtain ⟨v_f_fc, hv_f_mem, hv_f_S⟩ :=
            hres.dep_closure _ h_feat_pn _ _ (mem_cfDeps_a_depToInterFeat hdep hf')
          obtain ⟨v_f, hv_f_vs, rfl⟩ := Finset.mem_map.mp hv_f_mem
          -- back-edge: secondary at v_f → shared at v_f.
          have hshared_v_f_S : (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v_f) ∈ S := by
            simpa using hres.dep_closure _ hv_f_S _ _ (mem_cfDeps_a_interFeatToInter hdep hv_f_vs hf')
          -- version_unique on shared intermediate: shared at v_f = shared at v₀.
          have hver : hcvr.origV v_f = hcvr.origV v₀ :=
            hres.version_unique _ _ _ hshared_v_f_S hv_fc_S
          have hv_eq : v_f = v₀ := hcvr.origV.injective hver
          subst hv_eq
          -- secondary at v₀ → feature granular at v₀.
          simpa using hres.dep_closure _ hv_f_S _ _ (mem_cfDeps_a_interToFeat hdep hv_f_vs hf')
        · rintro y ⟨hy_vs, _, hπ⟩
          exact hcvr.origV.injective (hres.version_unique _ _ _
            (cfSoundnessWitnessπ_inter_mem hπ) hv_fc_S)

omit hroot_no_support in
theorem cfSound_π_functional :
    ∀ n v v' p,
    ((n, v), p) ∈ cfSoundnessWitnessπ Δ_f Δ_a g S →
    ((n, v'), p) ∈ cfSoundnessWitnessπ Δ_f Δ_a g S → v = v' := by
  rintro n v v' ⟨p_n, p_v⟩ h1 h2
  exact hcvr.origV.injective (hres.version_unique _ _ _
    (cfSoundnessWitnessπ_inter_mem h1) (cfSoundnessWitnessπ_inter_mem h2))

omit hroot_no_support in
theorem cfSound_version_granularity :
    ∀ n v v' fs fs',
    ((n, v), fs) ∈ cfSoundnessWitnessS (N := N) (F := F) g S →
    ((n, v'), fs') ∈ cfSoundnessWitnessS (N := N) (F := F) g S → v ≠ v' → g v ≠ g v' := by
      intro n v v' fs fs' h1 h2 hv_ne hg_eq
      obtain ⟨n₁, v₁, hS₁, heq₁⟩ := mem_cfSoundnessWitnessS h1
      obtain ⟨n₂, v₂, hS₂, heq₂⟩ := mem_cfSoundnessWitnessS h2
      simp only [Prod.mk.injEq] at heq₁ heq₂
      obtain ⟨⟨rfl, rfl⟩, -⟩ := heq₁
      obtain ⟨⟨rfl, rfl⟩, -⟩ := heq₂
      rw [hg_eq] at hS₁
      exact hv_ne (hcvr.origV.injective (hres.version_unique _ _ _ hS₁ hS₂))

omit hroot_no_support in
theorem cfSound_support_mem :
    ∀ n v fs f, ((n, v), fs) ∈ cfSoundnessWitnessS (N := N) (F := F) g S →
    f ∈ fs → ((n, v), f) ∈ support := by
      intro n v fs f h₁ h₂;
      have h_concurrent_feature_real : (hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v) ∈ concurrentFeatureReal R support Δ_f Δ_a g := by
        have h_concurrent_feature_real : (hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v) ∈ S := by
          unfold cfSoundnessWitnessS at h₁;
          grind;
        exact hres.1 h_concurrent_feature_real;
      unfold concurrentFeatureReal at h_concurrent_feature_real;
      simp +decide [ Concurrent.embedReal ] at h_concurrent_feature_real;
      unfold Feature.featureReal at h_concurrent_feature_real; simp +decide [ Concurrent.embedPkg ] at h_concurrent_feature_real;
      rcases h_concurrent_feature_real with ⟨ a, ha | ⟨ a', b, c, h₁, h₂ ⟩, h₃ ⟩ <;> simp +decide [ hcnm.granularN_injective.eq_iff ] at h₃ ⊢;
      · unfold Feature.embedSet at ha; simp +decide [ h₃ ] at ha;
        unfold Feature.embedPkg at ha; simp +decide at ha;
      · split_ifs at h₂ <;> simp_all +decide [ Feature.HasFeatureNames.featuredN ]

end SoundnessFields

/-! ### Soundness -/

-- Paper Thm 5.1.3 (Concurrent Feature Reduction Soundness).
theorem concurrent_feature_soundness
    [Fintype F]
    (R : Real N V)
    (support : Feature.Support N V F)
    (Δ_f : Feature.FeatDepRel N V F) (Δ_a : Feature.AddlDepRel N V F)
    (g : V → G) (r : Package N V)
    (S : Finset (Package N_FC V_FC))
    (hres : IsResolution
      (concurrentFeatureReal R support Δ_f Δ_a g)
      (concurrentFeatureDeps R support Δ_f Δ_a g)
      (Concurrent.embedPkg g (Feature.embedPkg F r)) S)
    (hroot_no_support : ∀ f, (r, f) ∉ support) :
    ∃ S_cf π, IsConcurrentFeatureResolution R support Δ_f Δ_a g r S_cf π :=
  ⟨cfSoundnessWitnessS (N := N) (F := F) g S, cfSoundnessWitnessπ Δ_f Δ_a g S,
    ⟨hroot_no_support,
     cfSound_subset R support Δ_f Δ_a g r S hres,
     cfSound_root_mem R support Δ_f Δ_a g r S hres hroot_no_support,
     cfSound_feature_unification g S,
     cfSound_parent_closure R support Δ_f Δ_a g r S hres,
     cfSound_parent_closure_addl R support Δ_f Δ_a g r S hres,
     cfSound_π_functional R support Δ_f Δ_a g r S hres,
     cfSound_version_granularity R support Δ_f Δ_a g r S hres,
     cfSound_support_mem R support Δ_f Δ_a g r S hres⟩⟩

end PackageCalculus.Composition
