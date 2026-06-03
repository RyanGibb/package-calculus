import PackageCalculus.Extensions.Virtual.Reduction.Definition

/-! # Virtual extension: completeness

Any virtual resolution lifts to a core resolution of the virtual encoding. -/

namespace PackageCalculus.Virtual

open Classical

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVirtualNames N V N'] [hvv : HasVirtualVersions N V V']

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
private theorem embedPkg_inj {p q : Package N V}
    (h : @embedPkg N V N' V' _ _ p = embedPkg q) : p = q := by
  obtain ⟨pn, pv⟩ := p; obtain ⟨qn, qv⟩ := q
  simp only [embedPkg, Prod.mk.injEq] at h
  exact Prod.ext (hvn.origN.injective h.1) (hvv.origV.injective h.2)

noncomputable def selectorVersion
    (S_v : Finset (Package N V))
    (rho : Finset (Package N V × N × Package N V))
    (prov : ProvidesRel N V)
    (p : Package N V) (n : N) (vs : Finset V)
    (hp : hasProvider prov n vs) : V' :=
  if h : ∃ q, q ∈ S_v ∧ ∃ v, memTop v vs ∧ (q, n, v) ∈ prov ∧ (q, n, p) ∈ rho then
    hvv.providerV h.choose.1 h.choose.2
  else if h : ∃ u ∈ vs, (n, u) ∈ S_v then
    hvv.providerV n h.choose
  else
    hvv.providerV hp.choose.1 hp.choose.2

noncomputable def completenessWitness
    (Delta_v : DepRel N V)
    (prov : ProvidesRel N V)
    (S_v : Finset (Package N V))
    (rho : Finset (Package N V × N × Package N V)) :
    Finset (Package N' V') :=
  embedSet S_v ∪
  (Delta_v.filter (fun ⟨p, _, _⟩ => p ∈ S_v)).biUnion (fun ⟨p, n, vs⟩ =>
    if hp : hasProvider prov n vs then
      {(hvn.selectorN p n, selectorVersion S_v rho prov p n vs hp)}
    else ∅)

private theorem mem_cw_emb {Delta_v : DepRel N V} {prov : ProvidesRel N V}
    {S_v : Finset (Package N V)} {rho : Finset (Package N V × N × Package N V)}
    {p : Package N V} (hp : p ∈ S_v) :
    embedPkg p ∈ completenessWitness Delta_v prov S_v rho :=
  Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨p, hp, rfl⟩))

private theorem mem_cw_sel {Delta_v : DepRel N V} {prov : ProvidesRel N V}
    {S_v : Finset (Package N V)} {rho : Finset (Package N V × N × Package N V)}
    {p : Package N V} {n : N} {vs : Finset V}
    (hp : p ∈ S_v) (hd : (p, n, vs) ∈ Delta_v) (hprov : hasProvider prov n vs) :
    (hvn.selectorN p n, selectorVersion S_v rho prov p n vs hprov) ∈
      completenessWitness Delta_v prov S_v rho := by
  simp only [completenessWitness, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_filter]
  right
  refine ⟨⟨p, n, vs⟩, ⟨hd, hp⟩, ?_⟩
  simp [hprov]

-- Paper Thm 4.7.5 (Virtual Package Reduction Completeness).
theorem virtual_completeness
    (R_v : Real N V) (Delta_v : DepRel N V)
    (prov : ProvidesRel N V) (r : Package N V)
    (S_v : Finset (Package N V))
    (rho : Finset (Package N V × N × Package N V))
    (hres : IsVirtualResolution R_v Delta_v prov r S_v rho)
    (hfunc : ∀ p n vs₁ vs₂, (p, n, vs₁) ∈ Delta_v → (p, n, vs₂) ∈ Delta_v → vs₁ = vs₂) :
    IsResolution (virtualReal R_v Delta_v prov) (virtualDeps Delta_v R_v prov)
      (embedPkg r) (completenessWitness Delta_v prov S_v rho) := by
  -- Helper: selectorVersion ∈ selectorVersions
  have sel_in_svs : ∀ p ∈ S_v, ∀ n vs, (p, n, vs) ∈ Delta_v →
      ∀ hp : hasProvider prov n vs,
      selectorVersion S_v rho prov p n vs hp ∈
      selectorVersions R_v prov n vs := by
    intro p hpS n vs hd hp
    unfold selectorVersion
    split
    · rename_i hex
      obtain ⟨hqS, v, hmem, hprov_mem, hρ⟩ := hex.choose_spec
      simp only [selectorVersions, Finset.mem_union, Finset.mem_biUnion]
      left
      exact ⟨⟨hex.choose, n, v⟩, hprov_mem, by simp [hmem]⟩
    · rename_i hno_prov
      split
      · rename_i hex
        obtain ⟨hu_vs, hu_S⟩ := hex.choose_spec
        simp only [selectorVersions, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
        right; exact ⟨hex.choose, ⟨hu_vs, hres.subset hu_S⟩, rfl⟩
      · rename_i hno_dir
        exfalso
        rcases hres.virtual_dep_closure p hpS n vs hd with
          ⟨u, hu_vs, hu_S⟩ | ⟨q, ⟨hqS, v, hmem, hprov_q, hρ⟩, _⟩
        · exact hno_dir ⟨u, hu_vs, hu_S⟩
        · exact hno_prov ⟨q, hqS, v, hmem, hprov_q, hρ⟩
  -- Helper: selectorVersion gives (providerV m w) with (m, w) ∈ S_v
  have sel_mem_Sv : ∀ p ∈ S_v, ∀ n vs, (p, n, vs) ∈ Delta_v →
      ∀ hp : hasProvider prov n vs,
      ∃ m w, selectorVersion S_v rho prov p n vs hp = hvv.providerV m w ∧
        (m, w) ∈ S_v := by
    intro p hpS n vs hd hp
    unfold selectorVersion
    split
    · rename_i hex; exact ⟨_, _, rfl, hex.choose_spec.1⟩
    · rename_i hno_prov
      split
      · rename_i hex; exact ⟨n, hex.choose, rfl, hex.choose_spec.2⟩
      · rename_i hno_dir
        exfalso
        rcases hres.virtual_dep_closure p hpS n vs hd with
          ⟨u, hu_vs, hu_S⟩ | ⟨q, ⟨hqS, v, hmem, hprov_q, hρ⟩, _⟩
        · exact hno_dir ⟨u, hu_vs, hu_S⟩
        · exact hno_prov ⟨q, hqS, v, hmem, hprov_q, hρ⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- subset
    intro q hq
    simp only [completenessWitness, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image, embedSet] at hq
    rcases hq with ⟨p, hp, rfl⟩ | ⟨⟨p, n, vs⟩, ⟨hd, hpS⟩, hmem⟩
    · -- embedPkg p
      simp only [virtualReal, Finset.mem_union, Finset.mem_image, embedSet]
      left; left; exact ⟨p, hres.subset hp, rfl⟩
    · -- selector
      split at hmem <;> [skip; simp at hmem]
      rename_i hprov
      rw [Finset.mem_singleton] at hmem
      rw [hmem]
      unfold selectorVersion
      split
      · rename_i hex
        obtain ⟨hqS, v, hmem', hprov_mem, hρ⟩ := hex.choose_spec
        simp only [virtualReal, Finset.mem_union, Finset.mem_biUnion, embedSet]
        left; right
        refine ⟨⟨p, n, vs⟩, hd, ⟨⟨hex.choose, n, v⟩, hprov_mem, ?_⟩⟩
        simp [hmem']
      · rename_i hno_prov
        split
        · rename_i hex
          obtain ⟨hu_vs, hu_S⟩ := hex.choose_spec
          simp only [virtualReal, Finset.mem_union, Finset.mem_biUnion,
            Finset.mem_image, embedSet]
          right
          refine ⟨⟨p, n, vs⟩, hd, ?_⟩
          simp only [hprov]
          exact Finset.mem_image.mpr ⟨hex.choose, Finset.mem_filter.mpr ⟨hu_vs, hres.subset hu_S⟩, rfl⟩
        · rename_i hno_dir
          exfalso
          rcases hres.virtual_dep_closure p hpS n vs hd with
            ⟨u, hu_vs, hu_S⟩ | ⟨q, ⟨hqS, v, hmem', hprov_q, hρ⟩, _⟩
          · exact hno_dir ⟨u, hu_vs, hu_S⟩
          · exact hno_prov ⟨q, hqS, v, hmem', hprov_q, hρ⟩
  · -- root_mem
    exact mem_cw_emb hres.root_mem
  · -- dep_closure
    intro q hq m_dep dep_vs hd
    simp only [completenessWitness, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image, embedSet] at hq
    rcases hq with ⟨p, hp, rfl⟩ | ⟨⟨p, nd, vsd⟩, ⟨hd_orig, hpS⟩, hmem_sel⟩
    · -- Source is embedPkg p
      simp only [virtualDeps, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
        Finset.mem_biUnion] at hd
      rcases hd with (((⟨⟨p', n, vs⟩, ⟨hdep, hnp⟩, heq⟩ |
          ⟨⟨p', n, vs⟩, ⟨hdep, hprov⟩, heq⟩) |
          ⟨⟨p', n, vs⟩, hdep, ⟨⟨⟨m, w⟩, n'', v⟩, hprov_mem, hmem_if⟩⟩) |
          ⟨⟨p', n, vs⟩, hdep, hmem_if⟩)
      · -- No-provider case
        simp only [Prod.mk.injEq] at heq
        obtain ⟨heq_pkg, rfl, rfl⟩ := heq
        have hp_eq := embedPkg_inj heq_pkg
        subst hp_eq
        rcases hres.virtual_dep_closure p' hp n vs hdep with
          ⟨u, hu_vs, hu_S⟩ | ⟨q, ⟨hqS, vex, hmemtop, hpr, hρ⟩, _⟩
        · exact ⟨hvv.origV u, Finset.mem_map.mpr ⟨u, hu_vs, rfl⟩, mem_cw_emb hu_S⟩
        · exfalso; exact hnp ⟨q, vex, hpr, hmemtop⟩
      · -- With-provider case
        simp only [Prod.mk.injEq] at heq
        obtain ⟨heq_pkg, rfl, rfl⟩ := heq
        have hp_eq := embedPkg_inj heq_pkg
        subst hp_eq
        have hsel_in := sel_in_svs p' hp n vs hdep hprov
        exact ⟨selectorVersion S_v rho prov p' n vs hprov,
          hsel_in,
          mem_cw_sel hp hdep hprov⟩
      · -- Selector→provider: source is embedPkg → name contradiction
        split at hmem_if <;> [skip; simp at hmem_if]
        rw [Finset.mem_singleton] at hmem_if
        have h1 := (Prod.mk.inj (Prod.mk.inj hmem_if).1).1
        exact absurd h1 (hvn.origN_ne_selectorN _ _ _)
      · -- Selector→direct: source is embedPkg → name contradiction
        split at hmem_if <;> [skip; simp at hmem_if]
        simp only [Finset.mem_image, Finset.mem_filter] at hmem_if
        obtain ⟨_, _, hmem_eq⟩ := hmem_if
        have h1 := (Prod.mk.inj (Prod.mk.inj hmem_eq).1).1
        exact absurd h1 (hvn.selectorN_ne_origN _ _ _)
    · -- Source is selector package
      split at hmem_sel <;> [skip; simp at hmem_sel]
      rename_i hprov_orig
      rw [Finset.mem_singleton] at hmem_sel
      -- hmem_sel : q = (selectorN p nd, selectorVersion ...)
      rw [hmem_sel] at hd
      simp only [virtualDeps, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
        Finset.mem_biUnion] at hd
      rcases hd with (((⟨⟨p', n', vs'⟩, ⟨hdep', hnp'⟩, heq⟩ |
          ⟨⟨p', n', vs'⟩, ⟨hdep', hprov'⟩, heq⟩) |
          ⟨⟨p', n', vs'⟩, hdep', ⟨⟨⟨m, w⟩, n'', v⟩, hprov_mem, hmem_if⟩⟩) |
          ⟨⟨p', n', vs'⟩, hdep', hmem_if⟩)
      · -- No-provider: source is embedPkg → name contradiction
        simp only [embedPkg, Prod.mk.injEq] at heq
        exact absurd heq.1.1.symm (hvn.selectorN_ne_origN _ _ _)
      · -- With-provider: source is embedPkg → name contradiction
        simp only [embedPkg, Prod.mk.injEq] at heq
        exact absurd heq.1.1.symm (hvn.selectorN_ne_origN _ _ _)
      · -- Selector→provider
        split at hmem_if <;> [skip; simp at hmem_if]
        rw [Finset.mem_singleton] at hmem_if
        obtain ⟨h_src, rfl, rfl⟩ := Prod.mk.inj hmem_if
        obtain ⟨h1, h2⟩ := Prod.mk.inj h_src
        obtain ⟨hp_eq, hnd_eq⟩ := hvn.selectorN_injective h1
        subst hp_eq; subst hnd_eq
        -- Which variables survive?
        obtain ⟨m_sel, w_sel, heqv, hmw⟩ := sel_mem_Sv _ hpS _ vsd hd_orig hprov_orig
        rw [heqv] at h2
        obtain ⟨rfl, rfl⟩ := hvv.providerV_injective h2
        exact ⟨hvv.origV w_sel, Finset.mem_singleton.mpr rfl, mem_cw_emb hmw⟩
      · -- Selector→direct
        split at hmem_if <;> [skip; simp at hmem_if]
        simp only [Finset.mem_image, Finset.mem_filter] at hmem_if
        obtain ⟨u, _, hmem_eq⟩ := hmem_if
        obtain ⟨h_src, rfl, rfl⟩ := Prod.mk.inj hmem_eq
        obtain ⟨h1, h2⟩ := Prod.mk.inj h_src
        obtain ⟨hp_eq, hnd_eq⟩ := hvn.selectorN_injective h1
        subst hp_eq; subst hnd_eq
        obtain ⟨m_sel, w_sel, heqv, hmw⟩ := sel_mem_Sv _ hpS _ vsd hd_orig hprov_orig
        rw [heqv] at h2
        obtain ⟨rfl, rfl⟩ := hvv.providerV_injective h2
        exact ⟨hvv.origV _, Finset.mem_singleton.mpr rfl, mem_cw_emb hmw⟩
  · -- version_unique
    intro nm cv₁ cv₂ hv₁ hv₂
    simp only [completenessWitness, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image, embedSet] at hv₁ hv₂
    rcases hv₁ with ⟨p₁, hp₁, heq1⟩ | ⟨⟨p₁, n₁, vs₁⟩, ⟨hd₁, hpS₁⟩, hmem₁⟩ <;>
    rcases hv₂ with ⟨p₂, hp₂, heq2⟩ | ⟨⟨p₂, n₂, vs₂⟩, ⟨hd₂, hpS₂⟩, hmem₂⟩
    · -- embedPkg × embedPkg
      obtain ⟨h1n, h1v⟩ := Prod.mk.inj heq1
      obtain ⟨h2n, h2v⟩ := Prod.mk.inj heq2
      have hname : p₁.1 = p₂.1 := hvn.origN.injective (h1n.trans h2n.symm)
      have hvers := hres.version_unique p₁.1 p₁.2 p₂.2 hp₁ (hname ▸ hp₂)
      exact h1v.symm.trans ((congrArg hvv.origV hvers).trans h2v)
    · -- embedPkg × selector: name clash
      split at hmem₂ <;> [skip; simp at hmem₂]
      rw [Finset.mem_singleton] at hmem₂
      obtain ⟨h1n, _⟩ := Prod.mk.inj heq1
      obtain ⟨h2n, _⟩ := Prod.mk.inj hmem₂
      exact absurd (h1n.trans h2n) (hvn.origN_ne_selectorN _ _ _)
    · -- selector × embedPkg: name clash
      split at hmem₁ <;> [skip; simp at hmem₁]
      rw [Finset.mem_singleton] at hmem₁
      obtain ⟨h1n, _⟩ := Prod.mk.inj hmem₁
      obtain ⟨h2n, _⟩ := Prod.mk.inj heq2
      exact absurd (h2n.trans h1n) (hvn.origN_ne_selectorN _ _ _)
    · -- selector × selector: same (p, n) → same version (proof-irrelevant)
      split at hmem₁ <;> [skip; simp at hmem₁]
      split at hmem₂ <;> [skip; simp at hmem₂]
      rw [Finset.mem_singleton] at hmem₁ hmem₂
      obtain ⟨h1n, h1v⟩ := Prod.mk.inj hmem₁
      obtain ⟨h2n, h2v⟩ := Prod.mk.inj hmem₂
      obtain ⟨rfl, rfl⟩ := hvn.selectorN_injective (h1n.symm.trans h2n)
      have hvs := hfunc p₁ n₁ vs₁ vs₂ hd₁ hd₂; subst hvs
      exact h1v.trans h2v.symm

end PackageCalculus.Virtual
