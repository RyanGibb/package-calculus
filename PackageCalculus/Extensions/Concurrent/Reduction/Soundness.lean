import PackageCalculus.Extensions.Concurrent.Reduction.Definition
import Mathlib.Data.Finset.Preimage

/-! # Concurrent extension: soundness

Any core resolution of the concurrent encoding projects back to a valid
concurrent resolution of the original problem. -/

namespace PackageCalculus.Concurrent

open Classical

set_option linter.unusedSectionVars false

variable {N : Type*} {V : Type*} {G : Type*}
variable {N' : Type*} {V' : Type*}
variable [DecidableEq N] [DecidableEq V] [DecidableEq G] [DecidableEq N'] [DecidableEq V']
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

private theorem embedPkg_injective (g : V → G) :
    Function.Injective (embedPkg (N := N) (N' := N') (V' := V') g) := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [embedPkg, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have ⟨hn, _⟩ := hcnm.granularN_injective h1
  have hv := hcvr.origV.injective h2
  exact Prod.ext hn hv

private noncomputable def preimageS (g : V → G) (S : Finset (Package N' V')) :
    Finset (Package N V) :=
  S.preimage (embedPkg g) (Set.InjOn.mono (Set.subset_univ _)
    (Function.Injective.injOn (embedPkg_injective g)))

private theorem mem_preimageS {g : V → G} {S : Finset (Package N' V')} {p : Package N V} :
    p ∈ preimageS g S ↔ embedPkg g p ∈ S := by
  simp [preimageS, Finset.mem_preimage]

/-- Construct the parent-witness relation π as a Finset from Δ_C and S. -/
private def soundnessπ (Δ_C : DepRel N V) (g : V → G)
    (S : Finset (Package N' V')) : Finset (Package N V × Package N V) :=
  Δ_C.biUnion (fun ⟨⟨n, v⟩, m, vs⟩ =>
    vs.filter (fun u =>
      (hcnm.granularN m (g u), hcvr.origV u) ∈ S ∧
      (hcnm.granularN n (g v), hcvr.origV v) ∈ S ∧
      (isSplit g vs → ∃ u₀ ∈ vs,
        (hcnm.intermediateN n v m, hcvr.granV (g u₀)) ∈ S ∧ g u = g u₀))
    |>.image (fun u => ((m, u), (n, v))))

private theorem mem_soundnessπ {Δ_C : DepRel N V} {g : V → G}
    {S : Finset (Package N' V')} {pair : Package N V × Package N V} :
    pair ∈ soundnessπ Δ_C g S ↔
    ∃ n v m vs u, ((n, v), m, vs) ∈ Δ_C ∧
      (hcnm.granularN n (g v), hcvr.origV v) ∈ S ∧
      u ∈ vs ∧ (hcnm.granularN m (g u), hcvr.origV u) ∈ S ∧
      (isSplit g vs → ∃ u₀ ∈ vs,
        (hcnm.intermediateN n v m, hcvr.granV (g u₀)) ∈ S ∧ g u = g u₀) ∧
      pair = ((m, u), (n, v)) := by
  simp only [soundnessπ, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨⟨n, v⟩, m, vs⟩, hdep, u, ⟨huv, huS, hvS, hspl⟩, rfl⟩
    exact ⟨n, v, m, vs, u, hdep, hvS, huv, huS, hspl, rfl⟩
  · rintro ⟨n, v, m, vs, u, hdep, hvS, huv, huS, hspl, rfl⟩
    exact ⟨⟨⟨n, v⟩, m, vs⟩, hdep, u, ⟨huv, huS, hvS, hspl⟩, rfl⟩

private theorem embedPkg_mem_concurrentReal {g : V → G} {p : Package N V}
    {R_C : Real N V} {Δ_C : DepRel N V}
    (h : embedPkg g p ∈ concurrentReal (N' := N') (V' := V') R_C Δ_C g) : p ∈ R_C := by
  simp only [concurrentReal, embedReal, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion] at h
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

private theorem mem_concurrentDeps_direct {Δ_C : DepRel N V} {g : V → G}
    {n : N} {v : V} {m : N} {vs : Finset V} {u₀ : V}
    (hdep : ((n, v), m, vs) ∈ Δ_C) (hdir : isDirect g vs) (hu₀ : u₀ ∈ vs) :
    ((hcnm.granularN n (g v), hcvr.origV v),
     hcnm.granularN m (g u₀),
     vs.map hcvr.origV) ∈ concurrentDeps (N' := N') (V' := V') Δ_C g := by
  simp only [concurrentDeps, Finset.mem_union, Finset.mem_biUnion]
  left; left; left
  refine ⟨⟨⟨n, v⟩, m, vs⟩, hdep, ?_⟩
  simp only
  rw [if_pos hdir]
  exact Finset.mem_image.mpr ⟨u₀, hu₀, rfl⟩

private theorem mem_concurrentDeps_split1 {Δ_C : DepRel N V} {g : V → G}
    {n : N} {v : V} {m : N} {vs : Finset V}
    (hdep : ((n, v), m, vs) ∈ Δ_C) (hspl : isSplit g vs) :
    ((hcnm.granularN n (g v), hcvr.origV v),
     hcnm.intermediateN n v m,
     (vs.image (fun u => g u)).map hcvr.granV) ∈
      concurrentDeps (N' := N') (V' := V') Δ_C g := by
  simp only [concurrentDeps, Finset.mem_union, Finset.mem_biUnion]
  left; left; right
  refine ⟨⟨⟨n, v⟩, m, vs⟩, hdep, ?_⟩
  simp only
  rw [if_pos hspl]
  exact Finset.mem_singleton.mpr rfl

private theorem mem_concurrentDeps_split2 {Δ_C : DepRel N V} {g : V → G}
    {n : N} {v : V} {m : N} {vs : Finset V} {u₀ : V}
    (hdep : ((n, v), m, vs) ∈ Δ_C) (hspl : isSplit g vs) (hu₀ : u₀ ∈ vs) :
    ((hcnm.intermediateN n v m, hcvr.granV (g u₀)),
     hcnm.granularN m (g u₀),
     (vs.filter (fun w => g w = g u₀)).map hcvr.origV) ∈
      concurrentDeps (N' := N') (V' := V') Δ_C g := by
  simp only [concurrentDeps, Finset.mem_union, Finset.mem_biUnion]
  left; right
  refine ⟨⟨⟨n, v⟩, m, vs⟩, hdep, ?_⟩
  simp only
  rw [if_pos hspl]
  exact Finset.mem_image.mpr ⟨u₀, hu₀, rfl⟩

private theorem mem_concurrentDeps_empty {Δ_C : DepRel N V} {g : V → G}
    {n : N} {v : V} {m : N}
    (hdep : ((n, v), m, (∅ : Finset V)) ∈ Δ_C) :
    ((hcnm.granularN n (g v), hcvr.origV v),
     hcnm.intermediateN n v m,
     (∅ : Finset V')) ∈ concurrentDeps (N' := N') (V' := V') Δ_C g := by
  simp only [concurrentDeps, Finset.mem_union, Finset.mem_biUnion]
  right
  refine ⟨⟨⟨n, v⟩, m, ∅⟩, hdep, ?_⟩
  exact Finset.mem_singleton.mpr rfl

theorem concurrent_soundness
    (R_C : Real N V) (Δ_C : DepRel N V)
    (g : V → G) (r : Package N V)
    (S : Finset (Package N' V'))
    (hres : IsResolution (concurrentReal R_C Δ_C g) (concurrentDeps Δ_C g)
      (embedPkg g r) S)
    (hfunc : Δ_C.FunctionalInName) :
    IsConcurrentResolution R_C Δ_C g r (preimageS g S) (soundnessπ Δ_C g S) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- subset
    intro p hp
    rw [mem_preimageS] at hp
    exact embedPkg_mem_concurrentReal (hres.subset hp)
  · -- root_mem
    rw [mem_preimageS]
    exact hres.root_mem
  · -- parent_closure
    intro ⟨pn, pv⟩ hp m vs hdep
    rw [mem_preimageS] at hp
    by_cases hemp : vs = ∅
    · -- EMPTY case: the reduced instance forbids selecting the depender
      subst hemp
      have hd := mem_concurrentDeps_empty (N' := N') (V' := V') (g := g) hdep
      obtain ⟨cv, hcvv, _⟩ := hres.dep_closure _ hp _ _ hd
      exact absurd hcvv (Finset.notMem_empty cv)
    by_cases hdir : isDirect g vs
    · -- DIRECT case
      obtain ⟨u₀, hu₀⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      have hd := mem_concurrentDeps_direct hdep hdir hu₀
      obtain ⟨cv, hcvv, hcvS⟩ := hres.dep_closure _ hp _ _ hd
      rw [Finset.mem_map] at hcvv
      obtain ⟨u, huv, rfl⟩ := hcvv
      have hgu : g u = g u₀ := hdir u u₀ huv hu₀
      have huS : (hcnm.granularN m (g u), hcvr.origV u) ∈ S := by rwa [hgu]
      refine ⟨u, ?_, ?_⟩
      · refine ⟨huv, mem_preimageS.mpr huS, ?_⟩
        rw [mem_soundnessπ]
        exact ⟨pn, pv, m, vs, u, hdep, hp, huv, huS,
          fun ⟨a, b, ha, hb, hne⟩ => absurd (hdir a b ha hb) hne, rfl⟩
      · intro u' ⟨hu'v, hu'S_pre, hpi'⟩
        rw [mem_preimageS] at hu'S_pre
        rw [mem_soundnessπ] at hpi'
        obtain ⟨_, _, _, _, _, _, _, _, _, _, heq⟩ := hpi'
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
        have hgu' : g u' = g u₀ := hdir u' u₀ hu'v hu₀
        exact hcvr.origV.injective
          (hres.version_unique _ _ _ (hgu' ▸ hu'S_pre) hcvS)
    · -- SPLIT case
      have hspl : isSplit g vs := by
        unfold isDirect at hdir; push_neg at hdir
        obtain ⟨u₁, u₂, hu₁, hu₂, hne⟩ := hdir
        exact ⟨u₁, u₂, hu₁, hu₂, hne⟩
      have hd1 := mem_concurrentDeps_split1 hdep hspl
      obtain ⟨cv₀, hcv₀v, hcv₀S⟩ := hres.dep_closure _ hp _ _ hd1
      rw [Finset.mem_map] at hcv₀v
      obtain ⟨w₀, hw₀mem, rfl⟩ := hcv₀v
      rw [Finset.mem_image] at hw₀mem
      obtain ⟨u₀, hu₀v, rfl⟩ := hw₀mem
      have hd2 := mem_concurrentDeps_split2 hdep hspl hu₀v
      obtain ⟨cv, hcvv, hcvS⟩ := hres.dep_closure _ hcv₀S _ _ hd2
      rw [Finset.mem_map] at hcvv
      obtain ⟨u, humem, rfl⟩ := hcvv
      rw [Finset.mem_filter] at humem
      obtain ⟨huv, hgu⟩ := humem
      have huS : (hcnm.granularN m (g u), hcvr.origV u) ∈ S := by rwa [hgu]
      refine ⟨u, ?_, ?_⟩
      · refine ⟨huv, mem_preimageS.mpr huS, ?_⟩
        rw [mem_soundnessπ]
        exact ⟨pn, pv, m, vs, u, hdep, hp, huv, huS,
          fun _ => ⟨u₀, hu₀v, hcv₀S, hgu⟩, rfl⟩
      · intro u' ⟨hu'v, hu'S_pre, hpi'⟩
        rw [mem_preimageS] at hu'S_pre
        rw [mem_soundnessπ] at hpi'
        obtain ⟨_, _, _, vs', _, hdep', _, _, _, hspl_cond', heq⟩ := hpi'
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
        have hvs' := hfunc _ _ _ _ hdep' hdep; subst hvs'
        obtain ⟨u₀', hu₀'v, hu₀'S, hgu'⟩ := hspl_cond' hspl
        have huu := hcvr.granV.injective
          (hres.version_unique _ _ _ hu₀'S hcv₀S)
        rw [huu] at hgu'
        have hu'S₀ : (hcnm.granularN m (g u₀), hcvr.origV u') ∈ S :=
          hgu' ▸ hu'S_pre
        exact hcvr.origV.injective (hres.version_unique _ _ _ hu'S₀ hcvS)
  · -- version_granularity
    intro n v v' hv hv' hne hge
    rw [mem_preimageS] at hv hv'
    exact hne (hcvr.origV.injective (hres.version_unique _ _ _ (hge ▸ hv) hv'))
  · -- parent_subset
    intro c p hcp
    rw [mem_soundnessπ] at hcp
    obtain ⟨n, v, m, vs, u, _, hvS, _, huS, _, heq⟩ := hcp
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨mem_preimageS.mpr huS, mem_preimageS.mpr hvS⟩

end PackageCalculus.Concurrent
