import PackageCalculus.Extensions.Virtual.Reduction.Definition
import Mathlib.Data.Finset.Preimage

/-! # Virtual extension: soundness

Any core resolution of the virtual encoding induces a virtual resolution of
the original problem. -/

namespace PackageCalculus.Virtual

open Classical

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVirtualNames N V N'] [hvv : HasVirtualVersions N V V']

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem embedPkg_injective :
    Function.Injective (embedPkg : Package N V → Package N' V') := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [embedPkg, Prod.mk.injEq] at h
  exact Prod.ext (hvn.origN.injective h.1) (hvv.origV.injective h.2)

private noncomputable def preimageS (S : Finset (Package N' V')) : Finset (Package N V) :=
  S.preimage embedPkg (Set.InjOn.mono (Set.subset_univ _)
    (Function.Injective.injOn embedPkg_injective))

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem mem_preimageS {S : Finset (Package N' V')} {p : Package N V} :
    p ∈ preimageS S ↔ embedPkg p ∈ S := by
  simp [preimageS, Finset.mem_preimage]

theorem embedPkg_mem_real {p : Package N V}
    {R_v : Real N V} {Delta_v : DepRel N V} {prov : ProvidesRel N V}
    (h : embedPkg p ∈ virtualReal R_v Delta_v prov) : p ∈ R_v := by
  have hemb : embedPkg p ∈ embedSet R_v := by
    simp only [virtualReal, Finset.mem_union] at h
    rcases h with (h1 | h2)
    · rcases h1 with (h1a | h1b)
      · exact h1a
      · exfalso
        simp only [Finset.mem_biUnion] at h1b
        obtain ⟨⟨p', n', vs'⟩, _, h1b'⟩ := h1b
        obtain ⟨⟨q', n'', v'⟩, _, h1b''⟩ := h1b'
        split at h1b''
        · rw [Finset.mem_singleton] at h1b''
          simp only [embedPkg, Prod.mk.injEq] at h1b''
          exact absurd h1b''.1 (hvn.origN_ne_selectorN p.1 p' n')
        · simp at h1b''
    · exfalso
      simp only [Finset.mem_biUnion] at h2
      obtain ⟨⟨p', n', vs'⟩, _, h2'⟩ := h2
      split at h2'
      · simp only [Finset.mem_image, Finset.mem_filter] at h2'
        obtain ⟨_, _, heq⟩ := h2'
        simp only [embedPkg, Prod.mk.injEq] at heq
        exact absurd heq.1.symm (hvn.origN_ne_selectorN p.1 p' n')
      · simp at h2'
  simp only [embedSet, Finset.mem_image] at hemb
  obtain ⟨q, hqR, hqeq⟩ := hemb
  rwa [embedPkg_injective hqeq] at hqR

/-- The explicit provider relation witnessing virtual soundness. -/
noncomputable def soundnessRho (Delta_v : DepRel N V) (prov : ProvidesRel N V)
    (S : Finset (Package N' V')) : Finset (Package N V × N × Package N V) :=
  Delta_v.biUnion (fun ⟨p, n, vs⟩ =>
    prov.biUnion (fun ⟨q, n', v⟩ =>
      if n' = n ∧ memTop v vs ∧ embedPkg p ∈ S ∧
        (hvn.selectorN p n, hvv.providerV q.1 q.2) ∈ S
      then {(q, n, p)} else ∅))

theorem virtual_soundness
    (R_v : Real N V) (Delta_v : DepRel N V)
    (prov : ProvidesRel N V) (r : Package N V)
    (S : Finset (Package N' V'))
    (hres : IsResolution (virtualReal R_v Delta_v prov) (virtualDeps Delta_v R_v prov)
      (embedPkg r) S) :
    IsVirtualResolution R_v Delta_v prov r (preimageS S) (soundnessRho Delta_v prov S) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- subset
    intro p hp
    rw [mem_preimageS] at hp
    exact embedPkg_mem_real (hres.subset hp)
  · -- root_mem
    rw [mem_preimageS]
    exact hres.root_mem
  · -- virtual_dep_closure
    intro ⟨pn, pv⟩ hp n vs hdep
    rw [mem_preimageS] at hp
    by_cases hprov : hasProvider prov n vs
    · -- Case: dependency has providers
      have hd_sel : (embedPkg (pn, pv), hvn.selectorN (pn, pv) n,
          selectorVersions R_v prov n vs) ∈
          virtualDeps Delta_v R_v prov := by
        simp only [virtualDeps, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
        left; left; right
        exact ⟨⟨(pn, pv), n, vs⟩, ⟨hdep, hprov⟩, rfl⟩
      obtain ⟨sv, hsv_mem, hsv_S⟩ := hres.dep_closure _ hp _ _ hd_sel
      simp only [selectorVersions, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_image, Finset.mem_filter] at hsv_mem
      rcases hsv_mem with ⟨⟨⟨m, u⟩, n', v⟩, hprov_mem, hmem_if⟩ |
          ⟨u, ⟨hu_vs, hu_R⟩, rfl⟩
      · -- Provider case
        split at hmem_if
        · rename_i hcond
          obtain ⟨hn'n, hmemtop⟩ := hcond
          rw [Finset.mem_singleton] at hmem_if
          rw [hmem_if] at hsv_S
          have hprov_mem' : ((m, u), n, v) ∈ prov := hn'n ▸ hprov_mem
          have hd_prov : ((hvn.selectorN (pn, pv) n, hvv.providerV m u),
              hvn.origN m, ({hvv.origV u} : Finset _)) ∈
              virtualDeps Delta_v R_v prov := by
            simp only [virtualDeps, Finset.mem_union, Finset.mem_biUnion]
            left; right
            refine ⟨⟨(pn, pv), n, vs⟩, hdep, ⟨⟨(m, u), n, v⟩, hprov_mem', ?_⟩⟩
            simp [hmemtop]
          obtain ⟨w, hw_mem, hw_S⟩ := hres.dep_closure _ hsv_S _ _ hd_prov
          rw [Finset.mem_singleton.mp hw_mem] at hw_S
          have hrho_mem : (((m, u) : Package N V), n, ((pn, pv) : Package N V)) ∈
              soundnessRho Delta_v prov S := by
            simp only [soundnessRho, Finset.mem_biUnion]
            refine ⟨⟨(pn, pv), n, vs⟩, hdep, ⟨⟨(m, u), n, v⟩, hprov_mem', ?_⟩⟩
            simp [hmemtop, hsv_S, hp]
          right
          refine ⟨(m, u), ⟨mem_preimageS.mpr hw_S, v, hmemtop, hprov_mem', hrho_mem⟩, ?_⟩
          intro ⟨m', u'⟩ ⟨hq'S, v', _, hprov_out, hρ⟩
          rw [mem_preimageS] at hq'S
          simp only [soundnessRho] at hρ
          have hρ' : _ ∈ Delta_v.biUnion _ := hρ
          simp only [Finset.mem_biUnion] at hρ'
          obtain ⟨⟨p', n_r, vs_r⟩, hdep_r, ⟨⟨q_r, n_r', v_r⟩, hprov_mem_r, hmem_if_r⟩⟩ := hρ'
          split at hmem_if_r
          · rename_i hcond_r
            obtain ⟨hn_r', hmemtop_r, _, hsel_S'⟩ := hcond_r
            rw [Finset.mem_singleton] at hmem_if_r
            -- hmem_if_r : ((m', u'), n, (pn, pv)) = (q_r, n_r, p')
            -- From the tagged rho element we extract equalities
            have hq_eq : q_r = (m', u') := (Prod.mk.inj hmem_if_r).1.symm
            have hn_tag : n_r = n := (Prod.mk.inj (Prod.mk.inj hmem_if_r).2).1.symm
            have hp_eq : p' = (pn, pv) := (Prod.mk.inj (Prod.mk.inj hmem_if_r).2).2.symm
            subst hq_eq; subst hp_eq
            -- hsel_S' references n_r; rewrite to n using hn_tag
            rw [hn_tag] at hsel_S'
            -- Now hsel_S' : (selectorN (pn, pv) n, providerV m' u') ∈ S
            have hveq := hres.version_unique (hvn.selectorN (pn, pv) n)
              (hvv.providerV m u) (hvv.providerV m' u') hsv_S hsel_S'
            obtain ⟨rfl, rfl⟩ := hvv.providerV_injective hveq
            rfl
          · simp at hmem_if_r
        · simp at hmem_if
      · -- Direct case
        have hd_dir : ((hvn.selectorN (pn, pv) n, hvv.providerV n u),
            hvn.origN n, ({hvv.origV u} : Finset _)) ∈
            virtualDeps Delta_v R_v prov := by
          simp only [virtualDeps, Finset.mem_union, Finset.mem_biUnion,
            Finset.mem_image, Finset.mem_filter]
          right
          refine ⟨⟨(pn, pv), n, vs⟩, hdep, ?_⟩
          simp [hprov, hu_vs, hu_R]
        obtain ⟨w, hw_mem, hw_S⟩ := hres.dep_closure _ hsv_S _ _ hd_dir
        rw [Finset.mem_singleton.mp hw_mem] at hw_S
        left
        exact ⟨u, hu_vs, mem_preimageS.mpr hw_S⟩
    · -- Case: no providers
      have hd : (embedPkg (pn, pv), hvn.origN n,
          vs.map hvv.origV) ∈ virtualDeps Delta_v R_v prov := by
        simp only [virtualDeps, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
        left; left; left
        exact ⟨⟨(pn, pv), n, vs⟩, ⟨hdep, hprov⟩, rfl⟩
      obtain ⟨v, hv_mem, hv_S⟩ := hres.dep_closure _ hp _ _ hd
      simp only [Finset.mem_map] at hv_mem
      obtain ⟨u, hu_vs, rfl⟩ := hv_mem
      left
      exact ⟨u, hu_vs, mem_preimageS.mpr hv_S⟩
  · -- version_unique
    intro n v v' hv hv'
    rw [mem_preimageS] at hv hv'
    exact hvv.origV.injective (hres.version_unique _ _ _ hv hv')
  · -- provider_subset
    intro ⟨m, u⟩ n ⟨pn, pv⟩ hρ
    simp only [soundnessRho] at hρ
    have hρ' : _ ∈ Delta_v.biUnion _ := hρ
    simp only [Finset.mem_biUnion] at hρ'
    obtain ⟨⟨p', n_r, vs_r⟩, hdep_r, ⟨⟨q_r, n_r', v_r⟩, hprov_r, hmem_if⟩⟩ := hρ'
    split at hmem_if
    · rename_i hcond
      obtain ⟨hn_eq, hmemtop, hpS, hselS⟩ := hcond
      rw [Finset.mem_singleton] at hmem_if
      -- hmem_if : ((m, u), n, (pn, pv)) = (q_r, n_r, p')
      have hq_eq : q_r = (m, u) := (Prod.mk.inj hmem_if).1.symm
      have hp_eq : p' = (pn, pv) := (Prod.mk.inj (Prod.mk.inj hmem_if).2).2.symm
      subst hq_eq; subst hp_eq
      have hn_eq' : n_r' = n_r := hn_eq
      have hmemtop' : memTop v_r vs_r := hmemtop
      have hpS' : embedPkg (pn, pv) ∈ S := hpS
      have hselS' : (hvn.selectorN (pn, pv) n_r, hvv.providerV m u) ∈ S := hselS
      rw [hn_eq'] at hprov_r
      refine ⟨?_, mem_preimageS.mpr hpS'⟩
      have hd_prov : ((hvn.selectorN (pn, pv) n_r, hvv.providerV m u),
          hvn.origN m, ({hvv.origV u} : Finset _)) ∈
          virtualDeps Delta_v R_v prov := by
        simp only [virtualDeps, Finset.mem_union, Finset.mem_biUnion]
        left; right
        refine ⟨⟨(pn, pv), n_r, vs_r⟩, hdep_r, ⟨⟨(m, u), n_r, v_r⟩, hprov_r, ?_⟩⟩
        simp [hmemtop']
      obtain ⟨w, hw_mem, hw_S⟩ := hres.dep_closure _ hselS' _ _ hd_prov
      rw [Finset.mem_singleton.mp hw_mem] at hw_S
      exact mem_preimageS.mpr hw_S
    · simp at hmem_if

end PackageCalculus.Virtual
