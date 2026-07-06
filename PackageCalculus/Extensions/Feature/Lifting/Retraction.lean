import PackageCalculus.Extensions.Feature.Lifting.Definition

namespace PackageCalculus.Feature

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {F : Type*} [DecidableEq F] [Fintype F]
variable {N' : Type*} [DecidableEq N'] [hfn : HasFeatureNames N F N']

/-! ## Round-trip theorem -/

omit [Fintype F] in
theorem liftReal_featureReal (R : Real N V) (support : Support N V F) :
    liftReal (hfn := hfn) (featureReal R support) = R := by
  ext p
  rw [mem_liftReal]
  simp only [featureReal, embedSet, embedPkg, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion]
  constructor
  · intro h
    rcases h with ⟨⟨qn, qv⟩, hqR, heq⟩ | ⟨a, _, hmem_ite⟩
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      have := hfn.origN.injective h1; subst this; subst h2
      exact hqR
    · split at hmem_ite
      · simp only [Finset.mem_singleton, Prod.mk.injEq] at hmem_ite
        exact absurd hmem_ite.1 (hfn.origN_ne_featuredN _ _ _)
      · simp at hmem_ite
  · intro hp
    exact Or.inl ⟨p, hp, rfl⟩

/-! ## Support, dependency- and additional-dependency-relation retraction -/

set_option linter.unusedSectionVars false

/-- `tryOrigN` rejects featured names. -/
private theorem tryOrigN_featuredN (n : N) (f : F) :
    hfn.tryOrigN (hfn.featuredN n f) = none := by
  cases h : hfn.tryOrigN (hfn.featuredN n f) with
  | none => rfl
  | some m => exact (hfn.origN_ne_featuredN _ _ _ (hfn.tryOrigN_some _ _ h)).elim

/-- `tryFeaturedN` rejects origin names. -/
private theorem tryFeaturedN_origN (n : N) :
    hfn.tryFeaturedN (hfn.origN n) = none := by
  cases h : hfn.tryFeaturedN (hfn.origN n) with
  | none => rfl
  | some p => exact (hfn.featuredN_ne_origN _ _ _ (hfn.tryFeaturedN_some _ _ h)).elim

/-- Membership in `featureDeps`, decomposed into its five edge families. -/
theorem mem_featureDeps_iff {R : Real N V} {support : Support N V F}
    {Δ_f : FeatDepRel N V F} {Δ_a : AddlDepRel N V F}
    {e : Package N' V × N' × Finset V} :
    e ∈ featureDeps R support Δ_f Δ_a ↔
      (∃ n v f, ((n, v), f) ∈ support ∧ (n, v) ∈ R ∧
        e = ((hfn.featuredN n f, v), hfn.origN n, {v})) ∨
      (∃ p n vs, (p, n, vs, (∅ : Finset F)) ∈ Δ_f ∧
        e = (embedPkg F p, hfn.origN n, vs)) ∨
      (∃ p n vs fs, (p, n, vs, fs) ∈ Δ_f ∧ fs.Nonempty ∧ ∃ f ∈ fs,
        e = (embedPkg F p, hfn.featuredN n f, vs)) ∨
      (∃ n v f m vs, (((n, v), f), m, vs, (∅ : Finset F)) ∈ Δ_a ∧
        e = ((hfn.featuredN n f, v), hfn.origN m, vs)) ∨
      (∃ n v f m vs fs, (((n, v), f), m, vs, fs) ∈ Δ_a ∧ fs.Nonempty ∧ ∃ f' ∈ fs,
        e = ((hfn.featuredN n f, v), hfn.featuredN m f', vs)) := by
  simp only [featureDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_filter, Prod.exists]
  constructor
  · rintro ((((⟨n, v, f, hmem, hif⟩ | ⟨p₁, p₂, n, vs, fs, ⟨hmem, hfs⟩, heq⟩) |
      ⟨p₁, p₂, n, vs, fs, ⟨hmem, hfs⟩, f, hf, heq⟩) |
      ⟨n, v, f, m, vs, fs, ⟨hmem, hfs⟩, heq⟩) |
      ⟨n, v, f, m, vs, fs, ⟨hmem, hfs⟩, f', hf', heq⟩)
    · split at hif
      · rw [Finset.mem_singleton] at hif
        exact Or.inl ⟨n, v, f, hmem, ‹_›, hif⟩
      · exact absurd hif (Finset.notMem_empty e)
    · subst hfs
      exact Or.inr (Or.inl ⟨p₁, p₂, n, vs, hmem, heq.symm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p₁, p₂, n, vs, fs, hmem, hfs, f, hf, heq.symm⟩))
    · subst hfs
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, v, f, m, vs, hmem, heq.symm⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, v, f, m, vs, fs, hmem, hfs, f', hf', heq.symm⟩)))
  · rintro (⟨n, v, f, hmem, hR, rfl⟩ | ⟨p₁, p₂, n, vs, hmem, rfl⟩ |
      ⟨p₁, p₂, n, vs, fs, hmem, hfs, f, hf, rfl⟩ | ⟨n, v, f, m, vs, hmem, rfl⟩ |
      ⟨n, v, f, m, vs, fs, hmem, hfs, f', hf', rfl⟩)
    · refine Or.inl (Or.inl (Or.inl (Or.inl ⟨n, v, f, hmem, ?_⟩)))
      rw [if_pos hR]
      exact Finset.mem_singleton.mpr rfl
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨p₁, p₂, n, vs, ∅, ⟨hmem, rfl⟩, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨p₁, p₂, n, vs, fs, ⟨hmem, hfs⟩, f, hf, rfl⟩))
    · exact Or.inl (Or.inr ⟨n, v, f, m, vs, ∅, ⟨hmem, rfl⟩, rfl⟩)
    · exact Or.inr ⟨n, v, f, m, vs, fs, ⟨hmem, hfs⟩, f', hf', rfl⟩

/-! ### Evaluation of the edge decoders on canonical edges -/

private theorem embedPkg_injective {p q : Package N V}
    (h : embedPkg F (hfn := hfn) p = embedPkg F (hfn := hfn) q) : p = q := by
  simp only [embedPkg, Prod.mk.injEq] at h
  exact Prod.ext (hfn.origN.injective h.1) h.2

private theorem tryInvDepF0_eval {p : Package N V} {n : N} {vs : Finset V} :
    tryInvDepF0 (hfn := hfn) (embedPkg F p, hfn.origN n, vs) = some (p, n, vs, ∅) := by
  simp only [tryInvDepF0, embedPkg, hfn.tryOrigN_origN]

private theorem tryInvDepF1_eval {Δ' : DepRel N' V} {p : Package N V} {n : N} {f : F}
    {vs : Finset V} :
    tryInvDepF1 Δ' (embedPkg F p, hfn.featuredN n f, vs) =
      some (p, n, vs, gatherFs (F := F) Δ' p n vs) := by
  simp only [tryInvDepF1, embedPkg, hfn.tryOrigN_origN, hfn.tryFeaturedN_featuredN]

private theorem tryInvDepA0_eval {n : N} {v : V} {f : F} {m : N} {vs : Finset V} :
    tryInvDepA0 (hfn := hfn) ((hfn.featuredN n f, v), hfn.origN m, vs) =
      some (((n, v), f), m, vs, ∅) := by
  simp only [tryInvDepA0, hfn.tryFeaturedN_featuredN, hfn.tryOrigN_origN]

private theorem tryInvDepA1_eval {Δ' : DepRel N' V} {n : N} {v : V} {f : F} {m : N} {f' : F}
    {vs : Finset V} :
    tryInvDepA1 Δ' ((hfn.featuredN n f, v), hfn.featuredN m f', vs) =
      some (((n, v), f), m, vs, gatherAFs Δ' n v f m vs) := by
  simp only [tryInvDepA1, hfn.tryFeaturedN_featuredN]

theorem mem_baseDeps {R : Real N V} {support : Support N V F}
    {d : (Package N V × F) × N × Finset V × Finset F} :
    d ∈ baseDeps R support ↔
      ∃ n v f, ((n, v), f) ∈ support ∧ (n, v) ∈ R ∧ d = (((n, v), f), n, {v}, ∅) := by
  simp only [baseDeps, Finset.mem_biUnion]
  constructor
  · rintro ⟨s, hs, hd⟩
    split at hd
    · rw [Finset.mem_singleton] at hd
      obtain ⟨⟨n, v⟩, f⟩ := s
      exact ⟨n, v, f, hs, ‹_›, hd⟩
    · exact absurd hd (Finset.notMem_empty d)
  · rintro ⟨n, v, f, hs, hR, rfl⟩
    exact ⟨((n, v), f), hs, by rw [if_pos hR]; exact Finset.mem_singleton.mpr rfl⟩

/-! ### Gather lemmas -/

/-- For an entry of a `FunctionalInName` relation, `gatherFs` over the reduction
recovers exactly its required-feature set. -/
private theorem gatherFs_eq_of_mem {R : Real N V} {support : Support N V F}
    {Δ_f : FeatDepRel N V F} {Δ_a : AddlDepRel N V F} {p : Package N V} {n : N}
    {vs : Finset V} {fs : Finset F}
    (hmem : (p, n, vs, fs) ∈ Δ_f) (hfunc : Δ_f.FunctionalInName) :
    gatherFs (featureDeps R support Δ_f Δ_a) p n vs = fs := by
  ext f
  simp only [gatherFs, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hf
    rw [mem_featureDeps_iff] at hf
    rcases hf with ⟨n', v', f', _, _, heq⟩ | ⟨p', n', vs', _, heq⟩ |
      ⟨p', n', vs', fs', hmem', _, f₀, hf₀, heq⟩ | ⟨n', v', f', m', vs', _, heq⟩ |
      ⟨n', v', f', m', vs', fs', _, _, f₁, _, heq⟩
    · simp [embedPkg] at heq
    · simp [embedPkg] at heq
    · simp only [embedPkg, Prod.mk.injEq] at heq
      obtain ⟨⟨hp1, hp2⟩, hn, hv⟩ := heq
      obtain rfl : p = p' := Prod.ext (hfn.origN.injective hp1) hp2
      obtain ⟨rfl, rfl⟩ := hfn.featuredN_injective hn
      subst hv
      obtain ⟨_, rfl⟩ := hfunc p n vs fs vs fs' hmem hmem'
      exact hf₀
    · simp [embedPkg] at heq
    · simp [embedPkg] at heq
  · intro hf
    rw [mem_featureDeps_iff]
    exact Or.inr (Or.inr (Or.inl ⟨p, n, vs, fs, hmem, ⟨f, hf⟩, f, hf, rfl⟩))

/-- For an entry of a `FunctionalInName` additional-dependency relation,
`gatherAFs` over the reduction recovers exactly its required-feature set. -/
private theorem gatherAFs_eq_of_mem {R : Real N V} {support : Support N V F}
    {Δ_f : FeatDepRel N V F} {Δ_a : AddlDepRel N V F} {n : N} {v : V} {f : F} {m : N}
    {vs : Finset V} {fs : Finset F}
    (hmem : (((n, v), f), m, vs, fs) ∈ Δ_a) (hfunc : Δ_a.FunctionalInName) :
    gatherAFs (featureDeps R support Δ_f Δ_a) n v f m vs = fs := by
  ext f₂
  simp only [gatherAFs, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hf
    rw [mem_featureDeps_iff] at hf
    rcases hf with ⟨n', v', f', _, _, heq⟩ | ⟨p', n', vs', _, heq⟩ |
      ⟨p', n', vs', fs', _, _, f₀, _, heq⟩ | ⟨n', v', f', m', vs', _, heq⟩ |
      ⟨n', v', f', m', vs', fs', hmem', _, f₁, hf₁, heq⟩
    · simp at heq
    · simp [embedPkg] at heq
    · simp [embedPkg] at heq
    · simp at heq
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨hn, hv⟩, hm, hvs⟩ := heq
      obtain ⟨rfl, rfl⟩ := hfn.featuredN_injective hn
      obtain ⟨rfl, rfl⟩ := hfn.featuredN_injective hm
      subst hv
      subst hvs
      obtain ⟨_, rfl⟩ := hfunc ((n, v), f) m vs fs vs fs' hmem hmem'
      exact hf₁
  · intro hf
    rw [mem_featureDeps_iff]
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, v, f, m, vs, fs, hmem, ⟨f₂, hf⟩, f₂, hf, rfl⟩)))

/-! ### Soundness of the decoders on reduced dependency relations -/

/-- Membership in `featureReal`, decomposed into its two package families. -/
theorem mem_featureReal_iff {R : Real N V} {support : Support N V F} {q : Package N' V} :
    q ∈ featureReal R support ↔
      (∃ p ∈ R, q = embedPkg F p) ∨
      (∃ n v f, ((n, v), f) ∈ support ∧ (n, v) ∈ R ∧ q = (hfn.featuredN n f, v)) := by
  simp only [featureReal, embedSet, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Prod.exists]
  constructor
  · rintro (⟨p₁, p₂, hp, heq⟩ | ⟨n, v, f, hs, hif⟩)
    · exact Or.inl ⟨p₁, p₂, hp, heq.symm⟩
    · split at hif
      · rw [Finset.mem_singleton] at hif
        exact Or.inr ⟨n, v, f, hs, ‹_›, hif⟩
      · exact absurd hif (Finset.notMem_empty q)
  · rintro (⟨p₁, p₂, hp, rfl⟩ | ⟨n, v, f, hs, hR, rfl⟩)
    · exact Or.inl ⟨p₁, p₂, hp, rfl⟩
    · refine Or.inr ⟨n, v, f, hs, ?_⟩
      rw [if_pos hR]
      exact Finset.mem_singleton.mpr rfl

theorem mem_liftSupport {R' : Real N' V} {n : N} {v : V} {f : F} :
    ((n, v), f) ∈ liftSupport (hfn := hfn) R' ↔ (hfn.featuredN n f, v) ∈ R' := by
  simp only [liftSupport, Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def]
  constructor
  · rintro ⟨p, hp, hinv⟩
    rw [tryInvSupp, Option.map_eq_some_iff] at hinv
    obtain ⟨⟨n₀, f₀⟩, htry, heq⟩ := hinv
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨hn, hp2⟩, hf0⟩ := heq
    rw [hn, hf0] at htry
    have hp1 := hfn.tryFeaturedN_some _ _ htry
    have hpe : ((hfn.featuredN n f, v) : Package N' V) = p := Prod.ext hp1 hp2.symm
    rwa [hpe]
  · intro hp
    refine ⟨(hfn.featuredN n f, v), hp, ?_⟩
    rw [tryInvSupp]
    simp [hfn.tryFeaturedN_featuredN]

/-- Only no-feature parameterised edges are inverted by `tryInvDepF0`, to
genuine entries of `Δ_f`. -/
private theorem sound_depF0 {R : Real N V} {support : Support N V F}
    {Δ_f : FeatDepRel N V F} {Δ_a : AddlDepRel N V F}
    {e : Package N' V × N' × Finset V} {d : Package N V × N × Finset V × Finset F}
    (hmem : e ∈ featureDeps R support Δ_f Δ_a)
    (h : tryInvDepF0 (hfn := hfn) e = some d) : d ∈ Δ_f := by
  rw [mem_featureDeps_iff] at hmem
  rcases hmem with ⟨n, v, f, _, _, rfl⟩ | ⟨p, n, vs, hmem, rfl⟩ |
    ⟨p, n, vs, fs, _, _, f, _, rfl⟩ | ⟨n, v, f, m, vs, _, rfl⟩ |
    ⟨n, v, f, m, vs, fs, _, _, f', _, rfl⟩
  · simp only [tryInvDepF0, tryOrigN_featuredN] at h
    exact absurd h (by simp)
  · rw [tryInvDepF0_eval] at h
    obtain rfl := Option.some.inj h
    exact hmem
  · simp only [tryInvDepF0, embedPkg, hfn.tryOrigN_origN, tryOrigN_featuredN] at h
    exact absurd h (by simp)
  · simp only [tryInvDepF0, tryOrigN_featuredN] at h
    exact absurd h (by simp)
  · simp only [tryInvDepF0, tryOrigN_featuredN] at h
    exact absurd h (by simp)

/-- Only featured parameterised edges are inverted by `tryInvDepF1`, to genuine
entries of `Δ_f` (via `gatherFs`). -/
private theorem sound_depF1 {R : Real N V} {support : Support N V F}
    {Δ_f : FeatDepRel N V F} {Δ_a : AddlDepRel N V F}
    {e : Package N' V × N' × Finset V} {d : Package N V × N × Finset V × Finset F}
    (hfunc : Δ_f.FunctionalInName) (hmem : e ∈ featureDeps R support Δ_f Δ_a)
    (h : tryInvDepF1 (featureDeps R support Δ_f Δ_a) e = some d) : d ∈ Δ_f := by
  rw [mem_featureDeps_iff] at hmem
  rcases hmem with ⟨n, v, f, _, _, rfl⟩ | ⟨p, n, vs, hmem, rfl⟩ |
    ⟨p, n, vs, fs, hmem, _, f, _, rfl⟩ | ⟨n, v, f, m, vs, _, rfl⟩ |
    ⟨n, v, f, m, vs, fs, _, _, f', _, rfl⟩
  · simp only [tryInvDepF1, tryOrigN_featuredN] at h
    exact absurd h (by simp)
  · simp only [tryInvDepF1, embedPkg, hfn.tryOrigN_origN, tryFeaturedN_origN] at h
    exact absurd h (by simp)
  · rw [tryInvDepF1_eval] at h
    obtain rfl := Option.some.inj h
    rw [gatherFs_eq_of_mem hmem hfunc]
    exact hmem
  · simp only [tryInvDepF1, tryOrigN_featuredN] at h
    exact absurd h (by simp)
  · simp only [tryInvDepF1, tryOrigN_featuredN] at h
    exact absurd h (by simp)

/-- No-feature additional edges are inverted by `tryInvDepA0` to genuine entries
of `Δ_a` — or to automatic base requirements, with which they alias. -/
private theorem sound_depA0 {R : Real N V} {support : Support N V F}
    {Δ_f : FeatDepRel N V F} {Δ_a : AddlDepRel N V F}
    {e : Package N' V × N' × Finset V} {d : (Package N V × F) × N × Finset V × Finset F}
    (hmem : e ∈ featureDeps R support Δ_f Δ_a)
    (h : tryInvDepA0 (hfn := hfn) e = some d) : d ∈ Δ_a ∪ baseDeps R support := by
  rw [mem_featureDeps_iff] at hmem
  rcases hmem with ⟨n, v, f, hs, hR, rfl⟩ | ⟨p, n, vs, _, rfl⟩ |
    ⟨p, n, vs, fs, _, _, f, _, rfl⟩ | ⟨n, v, f, m, vs, hmem, rfl⟩ |
    ⟨n, v, f, m, vs, fs, _, _, f', _, rfl⟩
  · rw [tryInvDepA0_eval] at h
    obtain rfl := Option.some.inj h
    exact Finset.mem_union_right _ (mem_baseDeps.mpr ⟨n, v, f, hs, hR, rfl⟩)
  · simp only [tryInvDepA0, embedPkg, tryFeaturedN_origN] at h
    exact absurd h (by simp)
  · simp only [tryInvDepA0, embedPkg, tryFeaturedN_origN] at h
    exact absurd h (by simp)
  · rw [tryInvDepA0_eval] at h
    obtain rfl := Option.some.inj h
    exact Finset.mem_union_left _ hmem
  · simp only [tryInvDepA0, hfn.tryFeaturedN_featuredN, tryOrigN_featuredN] at h
    exact absurd h (by simp)

/-- Featured additional edges are inverted by `tryInvDepA1` to genuine entries
of `Δ_a` (via `gatherAFs`). -/
private theorem sound_depA1 {R : Real N V} {support : Support N V F}
    {Δ_f : FeatDepRel N V F} {Δ_a : AddlDepRel N V F}
    {e : Package N' V × N' × Finset V} {d : (Package N V × F) × N × Finset V × Finset F}
    (hfunc : Δ_a.FunctionalInName) (hmem : e ∈ featureDeps R support Δ_f Δ_a)
    (h : tryInvDepA1 (featureDeps R support Δ_f Δ_a) e = some d) : d ∈ Δ_a := by
  rw [mem_featureDeps_iff] at hmem
  rcases hmem with ⟨n, v, f, _, _, rfl⟩ | ⟨p, n, vs, _, rfl⟩ |
    ⟨p, n, vs, fs, _, _, f, _, rfl⟩ | ⟨n, v, f, m, vs, _, rfl⟩ |
    ⟨n, v, f, m, vs, fs, hmem, _, f', _, rfl⟩
  · simp only [tryInvDepA1, hfn.tryFeaturedN_featuredN, tryFeaturedN_origN] at h
    exact absurd h (by simp)
  · simp only [tryInvDepA1, embedPkg, tryFeaturedN_origN] at h
    exact absurd h (by simp)
  · simp only [tryInvDepA1, embedPkg, tryFeaturedN_origN] at h
    exact absurd h (by simp)
  · simp only [tryInvDepA1, hfn.tryFeaturedN_featuredN, tryFeaturedN_origN] at h
    exact absurd h (by simp)
  · rw [tryInvDepA1_eval] at h
    obtain rfl := Option.some.inj h
    rw [gatherAFs_eq_of_mem hmem hfunc]
    exact hmem

/-! ### Retraction theorems -/

/-- **Retraction of the support relation.** The reduced repository determines
the grounded part of the support relation. -/
theorem liftSupport_featureReal (R : Real N V) (support : Support N V F) :
    liftSupport (hfn := hfn) (featureReal R support) =
      support.filter (fun s => s.1 ∈ R) := by
  ext s
  obtain ⟨⟨n, v⟩, f⟩ := s
  rw [mem_liftSupport, mem_featureReal_iff, Finset.mem_filter]
  constructor
  · rintro (⟨p, _, heq⟩ | ⟨n', v', f', hs, hR, heq⟩)
    · simp [embedPkg] at heq
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨hn, rfl⟩ := heq
      obtain ⟨rfl, rfl⟩ := hfn.featuredN_injective hn
      exact ⟨hs, hR⟩
  · rintro ⟨hs, hR⟩
    exact Or.inr ⟨n, v, f, hs, hR, rfl⟩

/-- For a `GroundedIn` support relation, the retraction is exact. -/
theorem liftSupport_featureReal_of_grounded (R : Real N V) (support : Support N V F)
    (hg : support.GroundedIn R) :
    liftSupport (hfn := hfn) (featureReal R support) = support := by
  rw [liftSupport_featureReal]
  exact Finset.filter_true_of_mem (fun s hs => hg s.1 s.2 hs)

/-- `baseDeps` only sees the grounded part of the support relation. -/
theorem baseDeps_filter (R : Real N V) (support : Support N V F) :
    baseDeps R (support.filter (fun s => s.1 ∈ R)) = baseDeps R support := by
  ext d
  rw [mem_baseDeps, mem_baseDeps]
  constructor
  · rintro ⟨n, v, f, hs, hR, rfl⟩
    exact ⟨n, v, f, (Finset.mem_filter.mp hs).1, hR, rfl⟩
  · rintro ⟨n, v, f, hs, hR, rfl⟩
    exact ⟨n, v, f, Finset.mem_filter.mpr ⟨hs, hR⟩, hR, rfl⟩

/-- **Retraction of the feature dependency relation.** No side-condition beyond
the standing Functional-in-Name normalisation. -/
theorem liftDepsF_featureDeps (R : Real N V) (support : Support N V F)
    (Δ_f : FeatDepRel N V F) (Δ_a : AddlDepRel N V F)
    (hfunc : Δ_f.FunctionalInName) :
    liftDepsF (featureDeps (hfn := hfn) R support Δ_f Δ_a) = Δ_f := by
  ext d
  simp only [liftDepsF, Finset.mem_biUnion, Finset.mem_union, Option.mem_toFinset,
    Option.mem_def]
  constructor
  · rintro ⟨e, he, hF | hF⟩
    · exact sound_depF0 he hF
    · exact sound_depF1 hfunc he hF
  · intro hd
    obtain ⟨p, n, vs, fs⟩ := d
    rcases Finset.eq_empty_or_nonempty fs with rfl | ⟨f, hf⟩
    · exact ⟨(embedPkg F p, hfn.origN n, vs),
        mem_featureDeps_iff.mpr (Or.inr (Or.inl ⟨p, n, vs, hd, rfl⟩)),
        Or.inl tryInvDepF0_eval⟩
    · refine ⟨(embedPkg F p, hfn.featuredN n f, vs),
        mem_featureDeps_iff.mpr
          (Or.inr (Or.inr (Or.inl ⟨p, n, vs, fs, hd, ⟨f, hf⟩, f, hf, rfl⟩))),
        Or.inr ?_⟩
      rw [tryInvDepF1_eval, gatherFs_eq_of_mem hd hfunc]

/-- **Normal-form retraction of the additional-dependency relation.** Without
any irredundancy hypothesis, the raw lift recovers `Δ_a` *up to the
base-requirement closure*: exactly the automatic base requirements of grounded
support facts are added, and nothing else. -/
theorem liftDepsARaw_featureDeps (R : Real N V) (support : Support N V F)
    (Δ_f : FeatDepRel N V F) (Δ_a : AddlDepRel N V F)
    (hfunc : Δ_a.FunctionalInName) :
    liftDepsARaw (featureDeps (hfn := hfn) R support Δ_f Δ_a) =
      Δ_a ∪ baseDeps R support := by
  ext d
  simp only [liftDepsARaw, Finset.mem_biUnion, Finset.mem_union, Option.mem_toFinset,
    Option.mem_def]
  constructor
  · rintro ⟨e, he, hA | hA⟩
    · have := sound_depA0 he hA
      rwa [Finset.mem_union] at this
    · exact Or.inl (sound_depA1 hfunc he hA)
  · rintro (hd | hd)
    · obtain ⟨⟨⟨n, v⟩, f⟩, m, vs, fs⟩ := d
      rcases Finset.eq_empty_or_nonempty fs with rfl | ⟨f', hf'⟩
      · exact ⟨((hfn.featuredN n f, v), hfn.origN m, vs),
          mem_featureDeps_iff.mpr
            (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, v, f, m, vs, hd, rfl⟩)))),
          Or.inl tryInvDepA0_eval⟩
      · refine ⟨((hfn.featuredN n f, v), hfn.featuredN m f', vs),
          mem_featureDeps_iff.mpr
            (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨n, v, f, m, vs, fs, hd, ⟨f', hf'⟩, f', hf', rfl⟩)))),
          Or.inr ?_⟩
        rw [tryInvDepA1_eval, gatherAFs_eq_of_mem hd hfunc]
    · rw [mem_baseDeps] at hd
      obtain ⟨n, v, f, hs, hR, rfl⟩ := hd
      exact ⟨((hfn.featuredN n f, v), hfn.origN n, {v}),
        mem_featureDeps_iff.mpr (Or.inl ⟨n, v, f, hs, hR, rfl⟩),
        Or.inl tryInvDepA0_eval⟩

/-- **Retraction of the additional-dependency relation.** For a
`BaseIrredundant` relation, subtracting the recomputed base requirements
recovers `Δ_a` on the nose. -/
theorem liftDepsA_featureDeps (R : Real N V) (support : Support N V F)
    (Δ_f : FeatDepRel N V F) (Δ_a : AddlDepRel N V F)
    (hfunc : Δ_a.FunctionalInName) (hirr : Δ_a.BaseIrredundant R support) :
    liftDepsA (featureReal (hfn := hfn) R support)
      (featureDeps R support Δ_f Δ_a) = Δ_a := by
  rw [liftDepsA, liftDepsARaw_featureDeps R support Δ_f Δ_a hfunc, liftReal_featureReal,
    liftSupport_featureReal, baseDeps_filter]
  ext d
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hd | hd, hnb⟩
    · exact hd
    · exact absurd hd hnb
  · intro hd
    refine ⟨Or.inl hd, fun hb => ?_⟩
    rw [mem_baseDeps] at hb
    obtain ⟨n, v, f, hs, hR, rfl⟩ := hb
    exact hirr n v f hs hR hd

/-- **Full instance-level retraction for the feature extension.** For a
grounded support relation and Functional-in-Name, base-irredundant dependency
relations, lifting the reduced package universe and dependency relation
recovers the original quadruple `(R_f, support, Δ_f, Δ_a)`. -/
theorem featureLift_featureReduce (R : Real N V) (support : Support N V F)
    (Δ_f : FeatDepRel N V F) (Δ_a : AddlDepRel N V F)
    (hg : support.GroundedIn R) (hf : Δ_f.FunctionalInName)
    (ha : Δ_a.FunctionalInName) (hirr : Δ_a.BaseIrredundant R support) :
    (liftReal (hfn := hfn) (featureReal R support),
     liftSupport (hfn := hfn) (featureReal R support),
     liftDepsF (featureDeps (hfn := hfn) R support Δ_f Δ_a),
     liftDepsA (featureReal (hfn := hfn) R support) (featureDeps R support Δ_f Δ_a))
      = (R, support, Δ_f, Δ_a) := by
  rw [liftReal_featureReal, liftSupport_featureReal_of_grounded R support hg,
    liftDepsF_featureDeps R support Δ_f Δ_a hf,
    liftDepsA_featureDeps R support Δ_f Δ_a ha hirr]

end PackageCalculus.Feature
