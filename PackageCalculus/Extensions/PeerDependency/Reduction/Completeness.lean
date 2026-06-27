import PackageCalculus.Extensions.PeerDependency.Reduction.Definition

/-! # Peer-dependency extension: completeness

Any peer resolution lifts to a core resolution of the peer-dependency
encoding. -/

namespace PackageCalculus.PeerDep

open Classical PackageCalculus

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : Type*} {V : Type*} {G : Type*}
variable {N' : Type*} {V' : Type*}
variable [DecidableEq N] [DecidableEq V] [DecidableEq G] [DecidableEq N'] [DecidableEq V']
variable [hcnm : Concurrent.HasConcurrentNames N V G N']
variable [hcvr : Concurrent.HasConcurrentVersions V G V']

def completenessWitness (S_Θ : Finset (Package N V))
    (π : Finset (Package N V × Package N V))
    (Δ_C : DepRel N V) (g : V → G) :
    Finset (Package N' V') :=
  -- Granular packages
  S_Θ.image (fun ⟨n, v⟩ => (hcnm.granularN n (g v), hcvr.origV v)) ∪
  -- Intermediate packages
  (Δ_C.biUnion (fun ⟨⟨n, v⟩, m, vs⟩ =>
    if (n, v) ∈ S_Θ then
      (vs.filter (fun u => (m, u) ∈ S_Θ ∧ ((m, u), (n, v)) ∈ π)).image
        (fun u => (hcnm.intermediateN n v m, hcvr.origV u))
    else ∅))

private theorem mem_gran {S_Θ : Finset (Package N V)}
    {π : Finset (Package N V × Package N V)}
    {Δ_C : DepRel N V} {g : V → G}
    {n : N} {v : V} (h : (n, v) ∈ S_Θ) :
    (hcnm.granularN n (g v), hcvr.origV v) ∈
      completenessWitness S_Θ π Δ_C g :=
  Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨⟨n, v⟩, h, rfl⟩))

private theorem mem_inter {S_Θ : Finset (Package N V)}
    {π : Finset (Package N V × Package N V)}
    {Δ_C : DepRel N V} {g : V → G}
    {n : N} {v : V} {m : N} {vs : Finset V} {u : V}
    (hdep : ((n, v), m, vs) ∈ Δ_C) (hnv : (n, v) ∈ S_Θ)
    (hmu : (m, u) ∈ S_Θ) (hu : u ∈ vs) (hπ : ((m, u), (n, v)) ∈ π) :
    (hcnm.intermediateN n v m, hcvr.origV u) ∈
      completenessWitness S_Θ π Δ_C g := by
  simp only [completenessWitness, Finset.mem_union, Finset.mem_biUnion]
  right
  refine ⟨⟨⟨n, v⟩, m, vs⟩, hdep, ?_⟩
  simp only; rw [if_pos hnv]
  exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hmu, hπ⟩, rfl⟩

private theorem completenessWitness_mem_cases {S_Θ : Finset (Package N V)}
    {π : Finset (Package N V × Package N V)}
    {Δ_C : DepRel N V} {g : V → G}
    {q : Package N' V'} (hq : q ∈ completenessWitness S_Θ π Δ_C g) :
    (∃ n v, (n, v) ∈ S_Θ ∧ q = (hcnm.granularN n (g v), hcvr.origV v)) ∨
    (∃ n v m vs u, ((n, v), m, vs) ∈ Δ_C ∧ (n, v) ∈ S_Θ ∧
      (m, u) ∈ S_Θ ∧ u ∈ vs ∧ ((m, u), (n, v)) ∈ π ∧
      q = (hcnm.intermediateN n v m, hcvr.origV u)) := by
  simp only [completenessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hq
  rcases hq with ⟨⟨n, v⟩, hmem, rfl⟩ | ⟨⟨⟨n, v⟩, m, vs⟩, hdep, hmem⟩
  · exact Or.inl ⟨n, v, hmem, rfl⟩
  · right
    simp only at hmem; split at hmem
    case isTrue hnv =>
      simp only [Finset.mem_image, Finset.mem_filter] at hmem
      obtain ⟨u, ⟨hu, hmu, hπ⟩, rfl⟩ := hmem
      exact ⟨n, v, m, vs, u, hdep, hnv, hmu, hu, hπ, rfl⟩
    case isFalse => exact (List.mem_nil_iff _ |>.mp hmem).elim

-- Paper Thm 4.3.5 (Peer Dependency Reduction Completeness).
theorem peer_completeness
    (R_C : Real N V) (Δ_C : DepRel N V)
    (Θ : PeerRel N V) (g : V → G) (r : Package N V)
    (S_Θ : Finset (Package N V))
    (π : Finset (Package N V × Package N V))
    (hres : IsPeerResolution R_C Δ_C Θ g r S_Θ π)
    (hfunc : Δ_C.FunctionalInName) :
    IsResolution (peerReal R_C Δ_C Θ g) (peerDeps Δ_C Θ g)
      (Concurrent.embedPkg g r) (completenessWitness S_Θ π Δ_C g) := by
  have hconc := hres.concurrent
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- subset
    intro q hq
    rcases completenessWitness_mem_cases hq with
      ⟨n, v, hmem, rfl⟩ | ⟨n, v, m, vs, u, hdep, hnv, hmu, hu, _, rfl⟩
    · simp only [peerReal, Concurrent.embedReal, Finset.mem_union, Finset.mem_image,
        Finset.mem_biUnion]
      left; left; exact ⟨⟨n, v⟩, hconc.subset hmem, rfl⟩
    · simp only [peerReal, Concurrent.embedReal, Finset.mem_union, Finset.mem_image,
        Finset.mem_biUnion]
      left; right
      refine ⟨⟨⟨n, v⟩, m, vs⟩, hdep, ?_⟩
      exact ⟨u, hu, rfl⟩
  · -- root_mem
    obtain ⟨rn, rv⟩ := r
    exact mem_gran hconc.root_mem
  · -- dep_closure
    intro q hq m_dep dep_vs hd
    rcases completenessWitness_mem_cases hq with
      ⟨n, v, hmem, rfl⟩ | ⟨n, v, m, vs, u, hdep, hnv, hmu, hu, hπ, rfl⟩
    · -- granular package (granular n (g v), orig v)
      simp only [peerDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hd
      rcases hd with ((⟨a, haΔ, heq⟩ | ⟨a, haΔ, hmem_d⟩) | ⟨a, haΔ, hmem_d⟩)
      · -- depender→intermediate
        obtain ⟨⟨n', v'⟩, m', vs'⟩ := a
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨h1, h2⟩, rfl, rfl⟩ := heq
        obtain ⟨rfl, _⟩ := hcnm.granularN_injective h1
        have h2' := hcvr.origV.injective h2; subst h2'
        obtain ⟨u, ⟨huv, hmuS, hmuπ⟩, _⟩ := hconc.parent_closure _ hmem _ _ haΔ
        exact ⟨hcvr.origV u, Finset.mem_map.mpr ⟨u, huv, rfl⟩,
          mem_inter haΔ hmem hmuS huv hmuπ⟩
      · -- intermediate→dependee: source is granular, contradiction
        obtain ⟨⟨n', v'⟩, m', vs'⟩ := a
        simp only [Finset.mem_image, Prod.mk.injEq] at hmem_d
        obtain ⟨_, _, ⟨⟨h1, _⟩, _, _⟩⟩ := hmem_d
        exact absurd h1 (hcnm.intermediateN_ne_granularN _ _ _ _ _)
      · -- peer through intermediate: source is granular, contradiction
        obtain ⟨⟨n', v'⟩, o', us'⟩ := a
        simp only [Finset.mem_biUnion, Finset.mem_filter] at hmem_d
        obtain ⟨u_peer, _, theta_entry, ⟨_, _⟩, hmem'⟩ := hmem_d
        obtain ⟨_, m'', ws''⟩ := theta_entry
        simp only at hmem'; split at hmem'
        case isTrue =>
          simp only [Finset.mem_singleton, Prod.mk.injEq] at hmem'
          obtain ⟨⟨h1, _⟩, _, _⟩ := hmem'
          exact absurd h1 (hcnm.granularN_ne_intermediateN _ _ _ _ _)
        case isFalse => exact (List.mem_nil_iff _ |>.mp hmem').elim
    · -- intermediate package (intermediate n v m, orig u)
      simp only [peerDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hd
      rcases hd with ((⟨a, haΔ, heq⟩ | ⟨a, haΔ, hmem_d⟩) | ⟨a, haΔ, hmem_d⟩)
      · -- depender→intermediate: source is intermediate, contradiction
        obtain ⟨⟨n', v'⟩, m', vs'⟩ := a
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨h1, _⟩, _, _⟩ := heq
        exact absurd h1 (hcnm.granularN_ne_intermediateN _ _ _ _ _)
      · -- intermediate→dependee
        obtain ⟨⟨n', v'⟩, m', vs'⟩ := a
        simp only [Finset.mem_image, Prod.mk.injEq] at hmem_d
        obtain ⟨u', hu'v, ⟨⟨h1, h2⟩, rfl, rfl⟩⟩ := hmem_d
        -- h1 : intermediateN n' v' m' = intermediateN n v m, h2 : origV u' = origV u
        obtain ⟨rfl, rfl, rfl⟩ := hcnm.intermediateN_injective _ _ _ _ _ _ h1
        have h2' := hcvr.origV.injective h2; subst h2'
        have hvs := hfunc _ _ _ _ hdep haΔ; subst hvs
        exact ⟨hcvr.origV u', Finset.mem_singleton.mpr rfl, mem_gran hmu⟩
      · -- peer through intermediate
        obtain ⟨⟨n', v'⟩, o', us'⟩ := a
        simp only [Finset.mem_biUnion, Finset.mem_filter] at hmem_d
        obtain ⟨u_peer, hu_peer, ⟨p_th, m_peer, ws_peer⟩, ⟨hΘ, heq_p⟩, hmem'⟩ := hmem_d
        simp only at heq_p hmem'
        subst heq_p
        split at hmem'
        case isTrue hne_cond =>
          simp only [Finset.mem_singleton, Prod.mk.injEq] at hmem'
          obtain ⟨⟨h1, h2⟩, hmdeq, hvseq⟩ := hmem'
          obtain ⟨rfl, rfl, rfl⟩ := hcnm.intermediateN_injective _ _ _ _ _ _ h1
          have h2' := hcvr.origV.injective h2; subst h2'
          subst hmdeq; subst hvseq
          obtain ⟨⟨p_ne, m_ne, vs_ne⟩, hmem_ne⟩ := hne_cond
          rw [Finset.mem_filter] at hmem_ne
          obtain ⟨hdep_ne, hp_eq, hm_eq⟩ := hmem_ne
          simp only at hp_eq hm_eq
          -- hp_eq : p_ne = (n, v), hm_eq : m_ne = m_peer
          subst hp_eq; subst hm_eq
          obtain ⟨w₀, ⟨hw₀v, hw₀S, hw₀π⟩, _⟩ :=
            hconc.parent_closure _ hnv m_ne vs_ne hdep_ne
          have hw₀_peer : w₀ ∈ ws_peer :=
            hres.peer_satisfaction _ hmu m_ne ws_peer hΘ _ hπ vs_ne hdep_ne
              w₀ hw₀v hw₀S hw₀π
          exact ⟨hcvr.origV w₀, Finset.mem_map.mpr ⟨w₀, hw₀_peer, rfl⟩,
            mem_inter hdep_ne hnv hw₀S hw₀v hw₀π⟩
        case isFalse => exact (List.mem_nil_iff _ |>.mp hmem').elim
  · -- version_unique
    intro nm cv₁ cv₂ hv₁ hv₂
    rcases completenessWitness_mem_cases hv₁ with
      ⟨n₁, v₁, hmem₁, heq1⟩ | ⟨n₁, vp₁, m₁, vs₁, u₁, hd₁, hnv₁, hmu₁, hu₁, hπ₁, heq1⟩ <;>
    rcases completenessWitness_mem_cases hv₂ with
      ⟨n₂, v₂, hmem₂, heq2⟩ | ⟨n₂, vp₂, m₂, vs₂, u₂, hd₂, hnv₂, hmu₂, hu₂, hπ₂, heq2⟩ <;>
    simp only [Prod.mk.injEq] at heq1 heq2
    · -- granular × granular
      obtain ⟨h1n, rfl⟩ := heq1; obtain ⟨h2n, rfl⟩ := heq2
      obtain ⟨rfl, h1g⟩ := hcnm.granularN_injective (h1n.symm.trans h2n)
      by_contra hne
      have hne' : v₁ ≠ v₂ := fun h => hne (congrArg (⇑hcvr.origV) h)
      exact hconc.version_granularity _ _ _ hmem₁ hmem₂ hne' h1g
    · -- granular × intermediate: name clash
      obtain ⟨h1n, _⟩ := heq1; obtain ⟨h2n, _⟩ := heq2
      exact absurd (h1n.symm.trans h2n) (hcnm.granularN_ne_intermediateN _ _ _ _ _)
    · -- intermediate × granular: name clash
      obtain ⟨h1n, _⟩ := heq1; obtain ⟨h2n, _⟩ := heq2
      exact absurd (h1n.symm.trans h2n) (hcnm.intermediateN_ne_granularN _ _ _ _ _)
    · -- intermediate × intermediate
      obtain ⟨h1n, rfl⟩ := heq1; obtain ⟨h2n, rfl⟩ := heq2
      obtain ⟨rfl, rfl, rfl⟩ := hcnm.intermediateN_injective _ _ _ _ _ _ (h1n.symm.trans h2n)
      have hvs := hfunc (n₁, vp₁) m₁ vs₁ vs₂ hd₁ hd₂; subst hvs
      obtain ⟨w, _, huniq⟩ := hconc.parent_closure _ hnv₁ _ _ hd₁
      have h1 := huniq u₁ ⟨hu₁, hmu₁, hπ₁⟩
      have h2 := huniq u₂ ⟨hu₂, hmu₂, hπ₂⟩
      exact congrArg (⇑hcvr.origV) (h1.trans h2.symm)

end PackageCalculus.PeerDep
