import PackageCalculus.Extensions.Concurrent.Lifting.Definition

namespace PackageCalculus.Concurrent

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {G : Type*} [DecidableEq G]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

/-! ## Round-trip theorems -/

theorem liftReal_concurrentReal (R : Real N V) (Δ : DepRel N V) (g : V → G) :
    liftReal g (concurrentReal (N' := N') (V' := V') R Δ g) = R := by
  ext p;
  rw [ mem_liftReal, concurrentReal ];
  simp +decide [ embedReal, embedPkg ];
  constructor;
  · rintro ( ⟨ a, ha, ha' ⟩ | ⟨ a, b, c, d, hd, hd' ⟩ );
    · have := hcnm.granularN_injective ha'; aesop;
    · split_ifs at hd' <;> simp_all +decide ;
  · exact fun hp => Or.inl ⟨ p.1, hp, rfl ⟩

/-! ## Dependency-relation retraction

We show `liftDeps g (concurrentDeps Δ_C g) = Δ_C` for `FunctionalInName` `Δ_C`. -/

/-- `tryGranularN` rejects intermediate names. -/
private theorem tryGranularN_intermediateN (n : N) (v : V) (m : N) :
    hcnm.tryGranularN (hcnm.intermediateN n v m) = none := by
  cases h : hcnm.tryGranularN (hcnm.intermediateN n v m) with
  | none => rfl
  | some p =>
    exact (hcnm.granularN_ne_intermediateN _ _ _ _ _ (hcnm.tryGranularN_some _ _ h)).elim

/-- `tryIntermediateN` rejects granular names. -/
private theorem tryIntermediateN_granularN (n : N) (gg : G) :
    hcnm.tryIntermediateN (hcnm.granularN n gg) = none := by
  cases h : hcnm.tryIntermediateN (hcnm.granularN n gg) with
  | none => rfl
  | some p =>
    exact (hcnm.intermediateN_ne_granularN _ _ _ _ _ (hcnm.tryIntermediateN_some _ _ h)).elim

theorem mem_decodeVS {g : V → G} {vs' : Finset V'} {w : V} :
    w ∈ decodeVS g vs' ↔ hcvr.origV w ∈ vs' := by
  simp only [decodeVS, Finset.mem_filterMap]
  constructor
  · rintro ⟨x, hx, htry⟩
    rw [hcvr.tryOrigV_some _ _ htry]; exact hx
  · exact fun h => ⟨hcvr.origV w, h, hcvr.tryOrigV_origV w⟩

theorem mem_gatherVs {g : V → G} {Δ' : DepRel N' V'} {I : N'} {w : V} :
    w ∈ gatherVs g Δ' I ↔ ∃ e ∈ Δ', e.1.1 = I ∧ hcvr.origV w ∈ e.2.2 := by
  simp only [gatherVs, Finset.mem_biUnion, Finset.mem_filter, mem_decodeVS]
  constructor
  · rintro ⟨e, ⟨he, hI⟩, hw⟩; exact ⟨e, he, hI, hw⟩
  · rintro ⟨e, he, hI, hw⟩; exact ⟨e, ⟨he, hI⟩, hw⟩

private theorem isSplit_of_not_isDirect {g : V → G} {vs : Finset V}
    (h : ¬ isDirect g vs) : isSplit g vs := by
  unfold isDirect at h; unfold isSplit; push_neg at h
  obtain ⟨u₁, u₂, h1, h2, hne⟩ := h; exact ⟨u₁, u₂, h1, h2, hne⟩

/-- Membership in `concurrentDeps`, decomposed into its four edge families. -/
theorem mem_concurrentDeps_iff {Δ_C : DepRel N V} {g : V → G}
    {e : Package N' V' × N' × Finset V'} :
    e ∈ concurrentDeps Δ_C g ↔
      (∃ n v m vs, ((n, v), m, vs) ∈ Δ_C ∧ isDirect g vs ∧ ∃ u ∈ vs,
        e = ((hcnm.granularN n (g v), hcvr.origV v), hcnm.granularN m (g u),
             vs.map hcvr.origV)) ∨
      (∃ n v m vs, ((n, v), m, vs) ∈ Δ_C ∧ isSplit g vs ∧
        e = ((hcnm.granularN n (g v), hcvr.origV v), hcnm.intermediateN n v m,
             (vs.image g).map hcvr.granV)) ∨
      (∃ n v m vs, ((n, v), m, vs) ∈ Δ_C ∧ isSplit g vs ∧ ∃ u ∈ vs,
        e = ((hcnm.intermediateN n v m, hcvr.granV (g u)), hcnm.granularN m (g u),
             (vs.filter (fun w => g w = g u)).map hcvr.origV)) ∨
      (∃ n v m vs, ((n, v), m, vs) ∈ Δ_C ∧ vs = ∅ ∧
        e = ((hcnm.granularN n (g v), hcvr.origV v), hcnm.intermediateN n v m,
             (∅ : Finset V'))) := by
  simp only [concurrentDeps, Finset.mem_union, Finset.mem_biUnion, Prod.exists]
  constructor
  · rintro (((⟨n, v, m, vs, hmem, hif⟩ | ⟨n, v, m, vs, hmem, hif⟩) |
      ⟨n, v, m, vs, hmem, hif⟩) | ⟨n, v, m, vs, hmem, hif⟩)
    · split at hif
      · obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hif
        exact Or.inl ⟨n, v, m, vs, hmem, ‹_›, u, hu, heq.symm⟩
      · exact absurd hif (Finset.notMem_empty e)
    · split at hif
      · exact Or.inr (Or.inl ⟨n, v, m, vs, hmem, ‹_›, Finset.mem_singleton.mp hif⟩)
      · exact absurd hif (Finset.notMem_empty e)
    · split at hif
      · obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hif
        exact Or.inr (Or.inr (Or.inl ⟨n, v, m, vs, hmem, ‹_›, u, hu, heq.symm⟩))
      · exact absurd hif (Finset.notMem_empty e)
    · split at hif
      · exact Or.inr (Or.inr (Or.inr ⟨n, v, m, vs, hmem, ‹_›, Finset.mem_singleton.mp hif⟩))
      · exact absurd hif (Finset.notMem_empty e)
  · rintro (⟨n, v, m, vs, hmem, hd, u, hu, rfl⟩ | ⟨n, v, m, vs, hmem, hs, rfl⟩ |
      ⟨n, v, m, vs, hmem, hs, u, hu, rfl⟩ | ⟨n, v, m, vs, hmem, he, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨n, v, m, vs, hmem,
        by rw [if_pos hd]; exact Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨n, v, m, vs, hmem,
        by rw [if_pos hs]; exact Finset.mem_singleton.mpr rfl⟩))
    · exact Or.inl (Or.inr ⟨n, v, m, vs, hmem,
        by rw [if_pos hs]; exact Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩)
    · exact Or.inr ⟨n, v, m, vs, hmem, by rw [if_pos he]; exact Finset.mem_singleton.mpr rfl⟩

/-- For a split entry, `gatherVs` over the reduction recovers exactly its
version set (using `FunctionalInName` to rule out foreign contributions). -/
theorem gatherVs_eq_of_mem {Δ_C : DepRel N V} {g : V → G} {n : N} {v : V} {m : N}
    {vs : Finset V} (hmem : ((n, v), m, vs) ∈ Δ_C) (hsplit : isSplit g vs)
    (hfunc : Δ_C.FunctionalInName) :
    gatherVs g (concurrentDeps Δ_C g) (hcnm.intermediateN n v m) = vs := by
  ext w
  rw [mem_gatherVs]
  constructor
  · rintro ⟨e, he, hI, hw⟩
    rw [mem_concurrentDeps_iff] at he
    rcases he with ⟨n', v', m', vs', _, _, u, _, rfl⟩ | ⟨n', v', m', vs', _, _, rfl⟩ |
      ⟨n', v', m', vs', hmem', _, u, _, rfl⟩ | ⟨n', v', m', vs', _, _, rfl⟩
    · exact absurd hI (hcnm.granularN_ne_intermediateN _ _ _ _ _)
    · exact absurd hI (hcnm.granularN_ne_intermediateN _ _ _ _ _)
    · obtain ⟨rfl, rfl, rfl⟩ := hcnm.intermediateN_injective _ _ _ _ _ _ hI
      obtain rfl : vs' = vs := hfunc _ _ _ _ hmem' hmem
      rw [Finset.mem_map] at hw
      obtain ⟨x, hx, hxeq⟩ := hw
      obtain rfl := hcvr.origV.injective hxeq
      exact (Finset.mem_filter.mp hx).1
    · exact absurd hI (hcnm.granularN_ne_intermediateN _ _ _ _ _)
  · intro hw
    refine ⟨((hcnm.intermediateN n v m, hcvr.granV (g w)), hcnm.granularN m (g w),
      (vs.filter (fun z => g z = g w)).map hcvr.origV), ?_, rfl, ?_⟩
    · rw [mem_concurrentDeps_iff]
      exact Or.inr (Or.inr (Or.inl ⟨n, v, m, vs, hmem, hsplit, w, hw, rfl⟩))
    · rw [Finset.mem_map]
      exact ⟨w, Finset.mem_filter.mpr ⟨hw, rfl⟩, rfl⟩

/-- `tryInvDirect` inverts a direct edge to its entry. -/
private theorem tryInvDirect_eval {g : V → G} {n : N} {v : V} {m : N} {vs : Finset V}
    {u : V} (hd : isDirect g vs) (hu : u ∈ vs) :
    tryInvDirect g ((hcnm.granularN n (g v), hcvr.origV v), hcnm.granularN m (g u),
      vs.map hcvr.origV) = some ((n, v), m, vs) := by
  rw [tryInvDirect]
  simp only [hcnm.tryGranularN_granularN, hcvr.tryOrigV_origV, decodeVS_map_origV,
    true_and]
  rw [if_pos ⟨⟨u, hu⟩, fun w hw => hd w u hw hu⟩]

/-- `tryInvEmpty` inverts an empty edge to its entry. -/
private theorem tryInvEmpty_eval {g : V → G} {n : N} {v : V} {m : N} :
    tryInvEmpty g ((hcnm.granularN n (g v), hcvr.origV v), hcnm.intermediateN n v m,
      (∅ : Finset V')) = some ((n, v), m, ∅) := by
  rw [tryInvEmpty]
  simp only [hcnm.tryGranularN_granularN, hcvr.tryOrigV_origV,
    hcnm.tryIntermediateN_intermediateN, and_self, if_true]

/-- Direct edges are inverted to genuine entries of `Δ_C`. -/
private theorem sound_direct {Δ_C : DepRel N V} {g : V → G}
    {e : Package N' V' × N' × Finset V'} {d : Package N V × N × Finset V}
    (hmem : e ∈ concurrentDeps Δ_C g) (h : tryInvDirect g e = some d) : d ∈ Δ_C := by
  rw [mem_concurrentDeps_iff] at hmem
  rcases hmem with ⟨n, v, m, vs, hmem, hd, u, hu, rfl⟩ | ⟨n, v, m, vs, hmem, _, rfl⟩ |
    ⟨n, v, m, vs, hmem, _, u, hu, rfl⟩ | ⟨n, v, m, vs, hmem, _, rfl⟩
  · rw [tryInvDirect_eval hd hu] at h
    obtain rfl := Option.some.inj h; exact hmem
  · simp only [tryInvDirect, hcnm.tryGranularN_granularN, hcvr.tryOrigV_origV,
      tryGranularN_intermediateN] at h
    exact absurd h (by simp)
  · simp only [tryInvDirect, tryGranularN_intermediateN] at h
    exact absurd h (by simp)
  · simp only [tryInvDirect, hcnm.tryGranularN_granularN, hcvr.tryOrigV_origV,
      tryGranularN_intermediateN] at h
    exact absurd h (by simp)

/-- Empty edges are inverted to genuine entries of `Δ_C`. -/
private theorem sound_empty {Δ_C : DepRel N V} {g : V → G}
    {e : Package N' V' × N' × Finset V'} {d : Package N V × N × Finset V}
    (hmem : e ∈ concurrentDeps Δ_C g) (h : tryInvEmpty g e = some d) : d ∈ Δ_C := by
  rw [mem_concurrentDeps_iff] at hmem
  rcases hmem with ⟨n, v, m, vs, hmem, _, u, hu, rfl⟩ | ⟨n, v, m, vs, hmem, hs, rfl⟩ |
    ⟨n, v, m, vs, hmem, _, u, hu, rfl⟩ | ⟨n, v, m, vs, hmem, he, rfl⟩
  · -- direct edge: dependee granular, so tryIntermediateN fails
    simp only [tryInvEmpty, hcnm.tryGranularN_granularN, hcvr.tryOrigV_origV,
      tryIntermediateN_granularN] at h
    exact absurd h (by simp)
  · -- split dep→intermediate: version set nonempty, so `= ∅` fails
    simp only [tryInvEmpty, hcnm.tryGranularN_granularN, hcvr.tryOrigV_origV,
      hcnm.tryIntermediateN_intermediateN] at h
    split at h
    · rename_i hcond
      obtain ⟨a, _, ha, _, _⟩ := hs
      rw [Finset.map_eq_empty, Finset.image_eq_empty] at hcond
      exact absurd hcond.1 (Finset.nonempty_iff_ne_empty.mp ⟨a, ha⟩)
    · exact absurd h (by simp)
  · -- split intermediate→dependee: depender intermediate, so tryGranularN fails
    simp only [tryInvEmpty, tryGranularN_intermediateN] at h
    exact absurd h (by simp)
  · -- empty edge: the canonical case
    subst he
    rw [tryInvEmpty_eval] at h
    obtain rfl := Option.some.inj h; exact hmem

/-- Intermediate→dependee edges are inverted (via `gatherVs`) to entries of `Δ_C`. -/
private theorem sound_intermediate {Δ_C : DepRel N V} {g : V → G}
    {e : Package N' V' × N' × Finset V'} {n : N} {v : V} {m : N}
    (hfunc : Δ_C.FunctionalInName) (hmem : e ∈ concurrentDeps Δ_C g)
    (h : hcnm.tryIntermediateN e.1.1 = some (n, v, m)) :
    ((n, v), m, gatherVs g (concurrentDeps Δ_C g) e.1.1) ∈ Δ_C := by
  have hI : hcnm.intermediateN n v m = e.1.1 := hcnm.tryIntermediateN_some _ _ h
  rw [mem_concurrentDeps_iff] at hmem
  rcases hmem with ⟨n', v', m', vs', _, _, u, _, rfl⟩ | ⟨n', v', m', vs', _, _, rfl⟩ |
    ⟨n', v', m', vs', hmem', hs, u, _, rfl⟩ | ⟨n', v', m', vs', _, _, rfl⟩
  · exact absurd hI.symm (hcnm.granularN_ne_intermediateN _ _ _ _ _)
  · exact absurd hI.symm (hcnm.granularN_ne_intermediateN _ _ _ _ _)
  · -- e.1.1 = intermediateN n' v' m'
    simp only at hI
    obtain ⟨rfl, rfl, rfl⟩ := hcnm.intermediateN_injective _ _ _ _ _ _ hI
    rw [gatherVs_eq_of_mem hmem' hs hfunc]
    exact hmem'
  · exact absurd hI.symm (hcnm.granularN_ne_intermediateN _ _ _ _ _)

/-- Split edges are inverted (via `gatherVs`) to entries of `Δ_C`. -/
private theorem sound_split {Δ_C : DepRel N V} {g : V → G}
    {e : Package N' V' × N' × Finset V'} {d : Package N V × N × Finset V}
    (hfunc : Δ_C.FunctionalInName) (hmem : e ∈ concurrentDeps Δ_C g)
    (h : tryInvSplit g (concurrentDeps Δ_C g) e = some d) : d ∈ Δ_C := by
  rw [tryInvSplit, Option.map_eq_some_iff] at h
  obtain ⟨⟨n, v, m⟩, hp, rfl⟩ := h
  exact sound_intermediate hfunc hmem hp

/-- **Instance-level retraction for the concurrent dependency relation.**
Lifting the reduced dependencies recovers the original (`FunctionalInName`)
concurrent dependency relation. -/
theorem liftDeps_concurrentDeps (Δ_C : DepRel N V) (g : V → G)
    (hfunc : Δ_C.FunctionalInName) :
    liftDeps g (concurrentDeps Δ_C g) = Δ_C := by
  ext d
  constructor
  · intro hd
    simp only [liftDeps, Finset.mem_biUnion, Finset.mem_union, Option.mem_toFinset,
      Option.mem_def] at hd
    rcases hd with ⟨e, he, (hdir | hemp) | hspl⟩
    · exact sound_direct he hdir
    · exact sound_empty he hemp
    · exact sound_split hfunc he hspl
  · intro hd
    obtain ⟨⟨n, v⟩, m, vs⟩ := d
    rw [liftDeps, Finset.mem_biUnion]
    by_cases hvs : vs = ∅
    · subst hvs
      refine ⟨((hcnm.granularN n (g v), hcvr.origV v), hcnm.intermediateN n v m, ∅), ?_, ?_⟩
      · rw [mem_concurrentDeps_iff]
        exact Or.inr (Or.inr (Or.inr ⟨n, v, m, ∅, hd, rfl, rfl⟩))
      · simp only [Finset.mem_union, Option.mem_toFinset, Option.mem_def]
        exact Or.inl (Or.inr tryInvEmpty_eval)
    · by_cases hdir : isDirect g vs
      · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hvs
        refine ⟨((hcnm.granularN n (g v), hcvr.origV v), hcnm.granularN m (g u),
          vs.map hcvr.origV), ?_, ?_⟩
        · rw [mem_concurrentDeps_iff]
          exact Or.inl ⟨n, v, m, vs, hd, hdir, u, hu, rfl⟩
        · simp only [Finset.mem_union, Option.mem_toFinset, Option.mem_def]
          exact Or.inl (Or.inl (tryInvDirect_eval hdir hu))
      · have hs := isSplit_of_not_isDirect hdir
        obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hvs
        refine ⟨((hcnm.intermediateN n v m, hcvr.granV (g u)), hcnm.granularN m (g u),
          (vs.filter (fun z => g z = g u)).map hcvr.origV), ?_, ?_⟩
        · rw [mem_concurrentDeps_iff]
          exact Or.inr (Or.inr (Or.inl ⟨n, v, m, vs, hd, hs, u, hu, rfl⟩))
        · simp only [Finset.mem_union, Option.mem_toFinset, Option.mem_def]
          refine Or.inr ?_
          rw [tryInvSplit]
          simp only [hcnm.tryIntermediateN_intermediateN, Option.map_some,
            gatherVs_eq_of_mem hd hs hfunc]

/-- **Full instance-level retraction for the concurrent extension.**
Lifting the reduced package universe and dependency relation recovers the
original pair `(R_C, Δ_C)`, for `FunctionalInName` `Δ_C`. -/
theorem concurrentLift_concurrentReduce (R_C : Real N V) (Δ_C : DepRel N V) (g : V → G)
    (hfunc : Δ_C.FunctionalInName) :
    (liftReal g (concurrentReal (N' := N') (V' := V') R_C Δ_C g),
     liftDeps g (concurrentDeps (N' := N') (V' := V') Δ_C g)) = (R_C, Δ_C) := by
  rw [liftReal_concurrentReal, liftDeps_concurrentDeps _ _ hfunc]

end PackageCalculus.Concurrent