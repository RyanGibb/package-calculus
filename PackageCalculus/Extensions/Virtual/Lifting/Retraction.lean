import PackageCalculus.Extensions.Virtual.Lifting.Definition

namespace PackageCalculus.Virtual

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVirtualNames N V N'] [hvv : HasVirtualVersions N V V']

/-! ## Round-trip theorems -/

theorem liftReal_virtualReal (R : Real N V) (Δ : DepRel N V)
    (prov : ProvidesRel N V) :
    liftReal (virtualReal (N' := N') (V' := V') R Δ prov) = R := by
  convert Set.ext _;
  rotate_left;
  exact Package N V;
  exact { p : Package N V | embedPkg p ∈ virtualReal R Δ prov };
  exact { p : Package N V | p ∈ R };
  · unfold virtualReal;
    simp +decide [ embedSet, embedPkg ];
    grind +suggestions;
  · simp +decide [ Finset.ext_iff, Set.ext_iff, mem_liftReal ]

/-! ## Dependency-relation retraction

The reduction keeps only the real direct versions of a with-provider entry, so
`lift ∘ reduce = id` is false; we prove the `restrictReal`-normalised statement
instead, mirroring the Versions retraction. -/

set_option linter.unusedSectionVars false

/-- `tryOrigN` rejects selector names. -/
private theorem tryOrigN_selectorN (p : Package N V) (n : N) :
    hvn.tryOrigN (hvn.selectorN p n) = none := by
  cases h : hvn.tryOrigN (hvn.selectorN p n) with
  | none => rfl
  | some m => exact (hvn.origN_ne_selectorN _ _ _ (hvn.tryOrigN_some _ _ h)).elim

/-- `trySelectorN` rejects origin names. -/
private theorem trySelectorN_origN (n : N) :
    hvn.trySelectorN (hvn.origN n) = none := by
  cases h : hvn.trySelectorN (hvn.origN n) with
  | none => rfl
  | some q => exact (hvn.selectorN_ne_origN _ _ _ (hvn.trySelectorN_some _ _ h)).elim

/-- Membership in `virtualDeps`, decomposed into its four edge families. -/
theorem mem_virtualDeps_iff {Δ : DepRel N V} {R : Real N V} {prov : ProvidesRel N V}
    {e : Package N' V' × N' × Finset V'} :
    e ∈ virtualDeps Δ R prov ↔
      (∃ p n vs, (p, n, vs) ∈ Δ ∧ ¬hasProvider prov n vs ∧
        e = (embedPkg p, hvn.origN n, vs.map hvv.origV)) ∨
      (∃ p n vs, (p, n, vs) ∈ Δ ∧ hasProvider prov n vs ∧
        e = (embedPkg p, hvn.selectorN p n, selectorVersions R prov n vs)) ∨
      (∃ p n vs, (p, n, vs) ∈ Δ ∧ ∃ m w v, ((m, w), n, v) ∈ prov ∧ memTop v vs ∧
        e = ((hvn.selectorN p n, hvv.providerV m w), hvn.origN m, {hvv.origV w})) ∨
      (∃ p n vs, (p, n, vs) ∈ Δ ∧ hasProvider prov n vs ∧ ∃ u ∈ vs, (n, u) ∈ R ∧
        e = ((hvn.selectorN p n, hvv.providerV n u), hvn.origN n, {hvv.origV u})) := by
  simp only [virtualDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_filter, Prod.exists]
  constructor
  · rintro (((⟨p₁, p₂, n, vs, ⟨hmem, hpr⟩, rfl⟩ | ⟨p₁, p₂, n, vs, ⟨hmem, hpr⟩, rfl⟩) |
      ⟨p₁, p₂, n, vs, hmem, m, w, n', v, hpv, hif⟩) | ⟨p₁, p₂, n, vs, hmem, hif⟩)
    · exact Or.inl ⟨p₁, p₂, n, vs, hmem, hpr, rfl⟩
    · exact Or.inr (Or.inl ⟨p₁, p₂, n, vs, hmem, hpr, rfl⟩)
    · split at hif
      · rename_i hc
        rw [Finset.mem_singleton] at hif
        rw [hc.1] at hpv
        exact Or.inr (Or.inr (Or.inl ⟨p₁, p₂, n, vs, hmem, m, w, v, hpv, hc.2, hif⟩))
      · exact absurd hif (Finset.notMem_empty e)
    · split at hif
      · rename_i hc
        rw [Finset.mem_image] at hif
        obtain ⟨u, hu, heq⟩ := hif
        rw [Finset.mem_filter] at hu
        exact Or.inr (Or.inr (Or.inr ⟨p₁, p₂, n, vs, hmem, hc, u, hu.1, hu.2, heq.symm⟩))
      · exact absurd hif (Finset.notMem_empty e)
  · rintro (⟨p₁, p₂, n, vs, hmem, hpr, rfl⟩ | ⟨p₁, p₂, n, vs, hmem, hpr, rfl⟩ |
      ⟨p₁, p₂, n, vs, hmem, m, w, v, hpv, hmt, rfl⟩ |
      ⟨p₁, p₂, n, vs, hmem, hpr, u, hu, hR, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨p₁, p₂, n, vs, ⟨hmem, hpr⟩, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨p₁, p₂, n, vs, ⟨hmem, hpr⟩, rfl⟩))
    · refine Or.inl (Or.inr ⟨p₁, p₂, n, vs, hmem, m, w, n, v, hpv, ?_⟩)
      rw [if_pos ⟨rfl, hmt⟩]
      exact Finset.mem_singleton.mpr rfl
    · refine Or.inr ⟨p₁, p₂, n, vs, hmem, ?_⟩
      rw [if_pos hpr, Finset.mem_image]
      exact ⟨u, Finset.mem_filter.mpr ⟨hu, hR⟩, rfl⟩

theorem mem_gatherVS {Δ' : DepRel N' V'} {p : Package N V} {n : N} {u : V} :
    u ∈ gatherVS Δ' p n ↔
      ∃ e ∈ Δ', e.1.1 = hvn.selectorN p n ∧ hvv.tryProviderV e.1.2 = some (n, u) := by
  simp only [gatherVS, Finset.mem_biUnion]
  constructor
  · rintro ⟨e, he, hif⟩
    split at hif
    · rename_i hsel
      cases htp : hvv.tryProviderV e.1.2 with
      | none =>
        simp only [tryGatherV, htp] at hif
        exact absurd hif (Finset.notMem_empty u)
      | some q =>
        obtain ⟨a, u'⟩ := q
        simp only [tryGatherV, htp] at hif
        split at hif
        · rename_i ha
          rw [Finset.mem_singleton] at hif
          subst ha; subst hif
          exact ⟨e, he, hsel, htp⟩
        · exact absurd hif (Finset.notMem_empty u)
    · exact absurd hif (Finset.notMem_empty u)
  · rintro ⟨e, he, hsel, htp⟩
    refine ⟨e, he, ?_⟩
    rw [if_pos hsel]
    simp only [tryGatherV, htp]
    exact Finset.mem_singleton.mpr rfl

/-- For a with-provider entry of a `FunctionalInName` relation over a
`NoSelfProvides` provides relation, `gatherVS` recovers exactly the real
direct versions. -/
theorem gatherVS_eq_of_mem {Δ : DepRel N V} {R : Real N V} {prov : ProvidesRel N V}
    {p : Package N V} {n : N} {vs : Finset V}
    (hmem : (p, n, vs) ∈ Δ) (hprov : hasProvider prov n vs)
    (hfunc : Δ.FunctionalInName) (hself : prov.NoSelfProvides) :
    gatherVS (virtualDeps Δ R prov) p n = vs.filter (fun u => (n, u) ∈ R) := by
  ext u
  rw [mem_gatherVS, Finset.mem_filter]
  constructor
  · rintro ⟨e, he, hsel, htp⟩
    rw [mem_virtualDeps_iff] at he
    rcases he with ⟨p', n', vs', _, _, rfl⟩ | ⟨p', n', vs', _, _, rfl⟩ |
      ⟨p', n', vs', hmem', m, w, v, hpv, hmt, rfl⟩ | ⟨p', n', vs', hmem', _, u', hu', hR', rfl⟩
    · exact absurd hsel (by simp [embedPkg])
    · exact absurd hsel (by simp [embedPkg])
    · obtain ⟨rfl, rfl⟩ := hvn.selectorN_injective hsel
      simp only [hvv.tryProviderV_providerV, Option.some.injEq, Prod.mk.injEq] at htp
      obtain ⟨rfl, rfl⟩ := htp
      exact absurd rfl (hself _ _ _ hpv)
    · obtain ⟨rfl, rfl⟩ := hvn.selectorN_injective hsel
      simp only [hvv.tryProviderV_providerV, Option.some.injEq, Prod.mk.injEq] at htp
      obtain ⟨-, rfl⟩ := htp
      obtain rfl := hfunc p' n' vs' vs hmem' hmem
      exact ⟨hu', hR'⟩
  · rintro ⟨hu, hR⟩
    refine ⟨((hvn.selectorN p n, hvv.providerV n u), hvn.origN n, {hvv.origV u}), ?_, rfl, ?_⟩
    · rw [mem_virtualDeps_iff]
      exact Or.inr (Or.inr (Or.inr ⟨p, n, vs, hmem, hprov, u, hu, hR, rfl⟩))
    · rw [hvv.tryProviderV_providerV]

/-! ### Evaluation and soundness of the decoders -/

private theorem tryInvDirect_eval {R : Real N V} {p : Package N V} {n : N} {vs : Finset V} :
    tryInvDirect R (embedPkg p, hvn.origN n, vs.map hvv.origV) =
      some (p, n, vs.filter (fun u => (n, u) ∈ R)) := by
  simp only [tryInvDirect, embedPkg, hvn.tryOrigN_origN, hvv.tryOrigV_origV,
    decodeVS_map_origV, if_true]

private theorem tryInvSelector_eval {Δ' : DepRel N' V'} {p : Package N V} {n : N}
    {ws : Finset V'} :
    tryInvSelector Δ' (embedPkg p, hvn.selectorN p n, ws) =
      some (p, n, gatherVS Δ' p n) := by
  simp only [tryInvSelector, embedPkg, hvn.tryOrigN_origN, hvv.tryOrigV_origV,
    hvn.trySelectorN_selectorN, if_true]

/-- No-provider edges are inverted by `tryInvDirect` to entries of the
`restrictReal`-normalised relation. -/
private theorem sound_direct {Δ : DepRel N V} {R : Real N V} {prov : ProvidesRel N V}
    {e : Package N' V' × N' × Finset V'} {d : Package N V × N × Finset V}
    (hmem : e ∈ virtualDeps Δ R prov) (h : tryInvDirect R e = some d) :
    d ∈ Δ.restrictReal R := by
  rw [mem_virtualDeps_iff] at hmem
  rcases hmem with ⟨p, n, vs, hmem, _, rfl⟩ | ⟨p, n, vs, _, _, rfl⟩ |
    ⟨p, n, vs, _, m, w, v, _, _, rfl⟩ | ⟨p, n, vs, _, _, u, _, _, rfl⟩
  · rw [tryInvDirect_eval] at h
    obtain rfl := Option.some.inj h
    exact Finset.mem_image.mpr ⟨(p, n, vs), hmem, rfl⟩
  · simp only [tryInvDirect, embedPkg, hvn.tryOrigN_origN, hvv.tryOrigV_origV,
      tryOrigN_selectorN] at h
    exact absurd h (by simp)
  · simp only [tryInvDirect, tryOrigN_selectorN] at h
    exact absurd h (by simp)
  · simp only [tryInvDirect, tryOrigN_selectorN] at h
    exact absurd h (by simp)

/-- With-provider depender→selector edges are inverted by `tryInvSelector` to
entries of the `restrictReal`-normalised relation. -/
private theorem sound_selector {Δ : DepRel N V} {R : Real N V} {prov : ProvidesRel N V}
    {e : Package N' V' × N' × Finset V'} {d : Package N V × N × Finset V}
    (hfunc : Δ.FunctionalInName) (hself : prov.NoSelfProvides)
    (hmem : e ∈ virtualDeps Δ R prov)
    (h : tryInvSelector (virtualDeps Δ R prov) e = some d) : d ∈ Δ.restrictReal R := by
  rw [mem_virtualDeps_iff] at hmem
  rcases hmem with ⟨p, n, vs, _, _, rfl⟩ | ⟨p, n, vs, hmem, hprov, rfl⟩ |
    ⟨p, n, vs, _, m, w, v, _, _, rfl⟩ | ⟨p, n, vs, _, _, u, _, _, rfl⟩
  · simp only [tryInvSelector, embedPkg, hvn.tryOrigN_origN, hvv.tryOrigV_origV,
      trySelectorN_origN] at h
    exact absurd h (by simp)
  · rw [tryInvSelector_eval] at h
    obtain rfl := Option.some.inj h
    rw [gatherVS_eq_of_mem hmem hprov hfunc hself]
    exact Finset.mem_image.mpr ⟨(p, n, vs), hmem, rfl⟩
  · simp only [tryInvSelector, tryOrigN_selectorN] at h
    exact absurd h (by simp)
  · simp only [tryInvSelector, tryOrigN_selectorN] at h
    exact absurd h (by simp)

/-- **`restrictReal`-normalised retraction for the virtual dependency
relation.** The reduction keeps only real direct dependee versions, so the
lift recovers the dependency relation up to `restrictReal` — exactly as the
Versions retraction — assuming the standing Functional-in-Name normalisation
and a `NoSelfProvides` provides relation. -/
theorem liftDeps_virtualDeps (R : Real N V) (Δ : DepRel N V) (prov : ProvidesRel N V)
    (hfunc : Δ.FunctionalInName) (hself : prov.NoSelfProvides) :
    liftDeps R (virtualDeps (N' := N') (V' := V') Δ R prov) = Δ.restrictReal R := by
  ext d
  simp only [liftDeps, Finset.mem_biUnion, Finset.mem_union, Option.mem_toFinset,
    Option.mem_def]
  constructor
  · rintro ⟨e, he, hD | hS⟩
    · exact sound_direct he hD
    · exact sound_selector hfunc hself he hS
  · intro hd
    rw [DepRel.restrictReal, Finset.mem_image] at hd
    obtain ⟨⟨p, n, vs⟩, hmem, rfl⟩ := hd
    by_cases hprov : hasProvider prov n vs
    · refine ⟨(embedPkg p, hvn.selectorN p n, selectorVersions R prov n vs), ?_, Or.inr ?_⟩
      · rw [mem_virtualDeps_iff]
        exact Or.inr (Or.inl ⟨p, n, vs, hmem, hprov, rfl⟩)
      · rw [tryInvSelector_eval, gatherVS_eq_of_mem hmem hprov hfunc hself]
    · refine ⟨(embedPkg p, hvn.origN n, vs.map hvv.origV), ?_, Or.inl ?_⟩
      · rw [mem_virtualDeps_iff]
        exact Or.inl ⟨p, n, vs, hmem, hprov, rfl⟩
      · rw [tryInvDirect_eval]

/-- **Combined `restrictReal`-normalised retraction for the virtual
extension.** Lifting the reduced package universe and dependency relation
recovers `(R, Δ.restrictReal R)`. -/
theorem virtualLift_virtualReduce (R : Real N V) (Δ : DepRel N V) (prov : ProvidesRel N V)
    (hfunc : Δ.FunctionalInName) (hself : prov.NoSelfProvides) :
    (liftReal (virtualReal (N' := N') (V' := V') R Δ prov),
     liftDeps (liftReal (virtualReal (N' := N') (V' := V') R Δ prov))
       (virtualDeps (N' := N') (V' := V') Δ R prov)) = (R, Δ.restrictReal R) := by
  rw [liftReal_virtualReal, liftDeps_virtualDeps R Δ prov hfunc hself]

end PackageCalculus.Virtual
