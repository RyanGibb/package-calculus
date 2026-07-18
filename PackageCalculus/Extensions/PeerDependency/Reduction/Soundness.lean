import PackageCalculus.Extensions.PeerDependency.Reduction.Definition
import Mathlib.Data.Finset.Preimage

/-! # Peer-dependency extension: soundness

Any core resolution of the peer-dependency encoding induces a peer
resolution of the original problem. -/

namespace PackageCalculus.PeerDep

open Classical PackageCalculus

set_option linter.unusedSectionVars false

variable {N : Type*} {V : Type*} {G : Type*}
variable {N' : Type*} {V' : Type*}
variable [DecidableEq N] [DecidableEq V] [DecidableEq G] [DecidableEq N'] [DecidableEq V']
variable [hcnm : Concurrent.HasConcurrentNames N V G N']
variable [hcvr : Concurrent.HasConcurrentVersions V G V']

private theorem embedPkg_injective (g : V → G) :
    Function.Injective (Concurrent.embedPkg (N := N) (N' := N') (V' := V') g) := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [Concurrent.embedPkg, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have ⟨hn, _⟩ := hcnm.granularN_injective h1
  have hv := hcvr.origV.injective h2
  exact Prod.ext hn hv

private noncomputable def preimageS (g : V → G) (S : Finset (Package N' V')) :
    Finset (Package N V) :=
  S.preimage (Concurrent.embedPkg g) (Set.InjOn.mono (Set.subset_univ _)
    (Function.Injective.injOn (embedPkg_injective g)))

private theorem mem_preimageS {g : V → G} {S : Finset (Package N' V')} {p : Package N V} :
    p ∈ preimageS g S ↔ Concurrent.embedPkg g p ∈ S := by
  simp [preimageS, Finset.mem_preimage]

/-- Construct the parent-witness relation π as a Finset from Δ_C and S. -/
private def soundnessπ (Δ_C : DepRel N V) (g : V → G)
    (S : Finset (Package N' V')) : Finset (Package N V × Package N V) :=
  Δ_C.biUnion (fun ⟨⟨n, v⟩, m, vs⟩ =>
    vs.filter (fun u =>
      (hcnm.intermediateN n v m, hcvr.origV u) ∈ S ∧
      (hcnm.granularN n (g v), hcvr.origV v) ∈ S)
    |>.image (fun u => ((m, u), (n, v))))

private theorem mem_soundnessπ {Δ_C : DepRel N V} {g : V → G}
    {S : Finset (Package N' V')} {pair : Package N V × Package N V} :
    pair ∈ soundnessπ Δ_C g S ↔
    ∃ n v m vs u, ((n, v), m, vs) ∈ Δ_C ∧
      (hcnm.granularN n (g v), hcvr.origV v) ∈ S ∧
      u ∈ vs ∧
      (hcnm.intermediateN n v m, hcvr.origV u) ∈ S ∧
      pair = ((m, u), (n, v)) := by
  simp only [soundnessπ, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨⟨n, v⟩, m, vs⟩, hdep, u, ⟨huv, hintS, hvS⟩, rfl⟩
    exact ⟨n, v, m, vs, u, hdep, hvS, huv, hintS, rfl⟩
  · rintro ⟨n, v, m, vs, u, hdep, hvS, huv, hintS, rfl⟩
    exact ⟨⟨⟨n, v⟩, m, vs⟩, hdep, u, ⟨huv, hintS, hvS⟩, rfl⟩

private theorem embedPkg_mem_peerReal {g : V → G} {p : Package N V}
    {R_C : Real N V} {Δ_C : DepRel N V} {Θ : PeerRel N V}
    (h : Concurrent.embedPkg g p ∈ peerReal (N' := N') (V' := V') R_C Δ_C Θ g) : p ∈ R_C := by
  simp only [peerReal, Concurrent.embedReal, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion] at h
  rcases h with ((⟨q, hqR, heq⟩ | ⟨a, _, hmem⟩) | ⟨a, _, hmem⟩)
  · simp only [Concurrent.embedPkg, Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have ⟨hn, _⟩ := hcnm.granularN_injective h1
    have hv := hcvr.origV.injective h2
    exact (Prod.ext hn hv : q = p) ▸ hqR
  · -- biUnion of intermediates
    obtain ⟨⟨n, v⟩, m, vs⟩ := a
    simp only [Concurrent.embedPkg, Prod.mk.injEq] at hmem
    obtain ⟨_, _, ⟨h1, _⟩⟩ := hmem
    exact absurd h1 (hcnm.intermediateN_ne_granularN _ _ _ _ _)
  · -- peer biUnion of intermediates
    obtain ⟨⟨n, v⟩, o, us⟩ := a
    simp only [Finset.mem_filter] at hmem
    obtain ⟨u_peer, _, ⟨theta_entry, ⟨hΘ, _⟩, hmem'⟩⟩ := hmem
    obtain ⟨_, m_peer, ws_peer⟩ := theta_entry
    split at hmem'
    · simp only [Finset.mem_image, Concurrent.embedPkg, Prod.mk.injEq] at hmem'
      obtain ⟨_, _, ⟨h1, _⟩⟩ := hmem'
      exact absurd h1 (hcnm.intermediateN_ne_granularN _ _ _ _ _)
    · simp at hmem'

private theorem mem_peerDeps_dep2int {Δ_C : DepRel N V} {Θ : PeerRel N V} {g : V → G}
    {n : N} {v : V} {m : N} {vs : Finset V}
    (hdep : ((n, v), m, vs) ∈ Δ_C) :
    ((hcnm.granularN n (g v), hcvr.origV v),
     hcnm.intermediateN n v m,
     vs.map hcvr.origV) ∈ peerDeps (N' := N') (V' := V') Δ_C Θ g := by
  simp only [peerDeps, Finset.mem_union, Finset.mem_image]
  left; left
  exact ⟨⟨⟨n, v⟩, m, vs⟩, hdep, rfl⟩

private theorem mem_peerDeps_int2dep {Δ_C : DepRel N V} {Θ : PeerRel N V} {g : V → G}
    {n : N} {v : V} {m : N} {vs : Finset V} {u₀ : V}
    (hdep : ((n, v), m, vs) ∈ Δ_C) (hu₀ : u₀ ∈ vs) :
    ((hcnm.intermediateN n v m, hcvr.origV u₀),
     hcnm.granularN m (g u₀),
     {hcvr.origV u₀}) ∈ peerDeps (N' := N') (V' := V') Δ_C Θ g := by
  simp only [peerDeps, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
  left; right
  exact ⟨⟨⟨n, v⟩, m, vs⟩, hdep, u₀, hu₀, rfl⟩

private theorem mem_peerDeps_peer {Δ_C : DepRel N V} {Θ : PeerRel N V} {g : V → G}
    {qn : N} {qv : V} {on : N} {vs₁ : Finset V} {m' : N} {ws' : Finset V} {ou : V}
    (hdep₁ : ((qn, qv), on, vs₁) ∈ Δ_C)
    (hu₁v : ou ∈ vs₁)
    (hpeer : ((on, ou), m', ws') ∈ Θ)
    (hparent : ∃ vs₂, ((qn, qv), m', vs₂) ∈ Δ_C) :
    ((hcnm.intermediateN qn qv on, hcvr.origV ou),
     hcnm.intermediateN qn qv m',
     ws'.map hcvr.origV) ∈ peerDeps (N' := N') (V' := V') Δ_C Θ g := by
  simp only [peerDeps, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
  right
  obtain ⟨vs₂, hdep₂⟩ := hparent
  refine ⟨⟨⟨qn, qv⟩, on, vs₁⟩, hdep₁, ou, hu₁v,
    ⟨⟨(on, ou), m', ws'⟩, ⟨hpeer, rfl⟩, ?_⟩⟩
  simp only
  have hne : (Δ_C.filter (fun ⟨p, m'', _⟩ => p = (qn, qv) ∧ m'' = m')).Nonempty :=
    ⟨⟨(qn, qv), m', vs₂⟩, Finset.mem_filter.mpr ⟨hdep₂, rfl, rfl⟩⟩
  rw [if_pos hne]
  exact Finset.mem_singleton.mpr rfl

theorem peer_soundness
    (R_C : Real N V) (Δ_C : DepRel N V)
    (Θ : PeerRel N V) (g : V → G) (r : Package N V)
    (S : Finset (Package N' V'))
    (hres : IsResolution (peerReal R_C Δ_C Θ g) (peerDeps Δ_C Θ g)
      (Concurrent.embedPkg g r) S) :
    IsPeerResolution R_C Δ_C Θ g r (preimageS g S) (soundnessπ Δ_C g S) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- subset
    intro p hp
    rw [mem_preimageS] at hp
    exact embedPkg_mem_peerReal (hres.subset hp)
  · -- root_mem
    rw [mem_preimageS]
    exact hres.root_mem
  · -- parent_closure
    intro ⟨pn, pv⟩ hp m vs hdep
    rw [mem_preimageS] at hp
    have hd1 := mem_peerDeps_dep2int (Θ := Θ) (g := g) hdep
    obtain ⟨cv₀, hcv₀v, hcv₀S⟩ := hres.dep_closure _ hp _ _ hd1
    rw [Finset.mem_map] at hcv₀v
    obtain ⟨u₀, hu₀v, rfl⟩ := hcv₀v
    -- (intermediate pn pv m, orig u₀) ∈ S
    have hd2 := mem_peerDeps_int2dep (Θ := Θ) (g := g) hdep hu₀v
    obtain ⟨w, hwu, hwS⟩ := hres.dep_closure _ hcv₀S _ _ hd2
    rw [Finset.mem_singleton] at hwu; subst hwu
    -- hwS : (granular m (g u₀), orig u₀) ∈ S
    refine ⟨u₀, ?_, ?_⟩
    · refine ⟨hu₀v, mem_preimageS.mpr hwS, ?_⟩
      rw [mem_soundnessπ]
      exact ⟨pn, pv, m, vs, u₀, hdep, hp, hu₀v, hcv₀S, rfl⟩
    · intro u' ⟨_, _, hpi'⟩
      rw [mem_soundnessπ] at hpi'
      obtain ⟨_, _, _, _, _, _, _, _, hintS', heq⟩ := hpi'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
      exact hcvr.origV.injective
        (hres.version_unique _ _ _ hintS' hcv₀S)
  · -- version_granularity
    intro n v v' hv hv' hne hge
    rw [mem_preimageS] at hv hv'
    exact hne (hcvr.origV.injective
      (hres.version_unique _ _ _ (hge ▸ hv) hv'))
  · -- parent_subset
    intro c p hcp
    rw [mem_soundnessπ] at hcp
    obtain ⟨n, v, m, vs, u, hdep, hvS, huv, hintS, heq⟩ := hcp
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    refine ⟨?_, mem_preimageS.mpr hvS⟩
    have hd2 := mem_peerDeps_int2dep (Θ := Θ) (g := g) hdep huv
    obtain ⟨w, hw_mem, hw_S⟩ := hres.dep_closure _ hintS _ _ hd2
    rw [Finset.mem_singleton.mp hw_mem] at hw_S
    exact mem_preimageS.mpr hw_S
  · -- peer_satisfaction
    intro ⟨on, ou⟩ hou m' ws' hpeer ⟨qn, qv⟩ hπ_mem us' hdep_q w hw_us hw_π
    rw [mem_preimageS] at hou
    rw [mem_soundnessπ] at hπ_mem hw_π
    -- From ((on, ou), (qn, qv)) ∈ π
    obtain ⟨_, _, _, vs₁, _, hdep₁, _, hu₁v, hintS₁, heq₁⟩ := hπ_mem
    simp only [Prod.mk.injEq] at heq₁
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq₁
    -- From ((m', w), (qn, qv)) ∈ π
    obtain ⟨_, _, _, vs₂, _, hdep₂, _, _, hintS₂, heq₂⟩ := hw_π
    simp only [Prod.mk.injEq] at heq₂
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq₂
    -- Peer dep edge
    have hd_peer := mem_peerDeps_peer (g := g) hdep₁ hu₁v hpeer ⟨vs₂, hdep₂⟩
    obtain ⟨w₁, hw₁_ws, hw₁_S⟩ := hres.dep_closure _ hintS₁ _ _ hd_peer
    rw [Finset.mem_map] at hw₁_ws
    obtain ⟨w₁', hw₁'_ws, rfl⟩ := hw₁_ws
    have hveq := hcvr.origV.injective
      (hres.version_unique _ _ _ hintS₂ hw₁_S)
    exact hveq ▸ hw₁'_ws

end PackageCalculus.PeerDep
