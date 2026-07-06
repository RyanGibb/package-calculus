import PackageCalculus.Extensions.PeerDependency.Lifting.Definition

namespace PackageCalculus.PeerDep

open PackageCalculus Concurrent

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {G : Type*} [DecidableEq G]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

/-! ## Round-trip theorems -/

theorem liftReal_peerReal (R : Real N V) (Δ : DepRel N V)
    (Θ : PeerRel N V) (g : V → G) :
    liftReal g (peerReal (N' := N') (V' := V') R Δ Θ g) = R := by
  ext p;
  rw [ mem_liftReal, peerReal ];
  simp +decide [ embedPkg, embedReal ];
  constructor;
  · rintro (⟨ a, ha, ha' ⟩ | ⟨ a, b, a₁, b₁, _, a₂, _, a₃, b₂, _, hmem ⟩);
    · have := hcnm.granularN_injective ha'; aesop;
    · split at hmem;
      · simp only [Finset.mem_image] at hmem;
        obtain ⟨ w, _, hw ⟩ := hmem;
        rw [Prod.ext_iff] at hw;
        exact absurd hw.1 (hcnm.intermediateN_ne_granularN _ _ _ _ _);
      · simp at hmem;
  · exact fun hp => Or.inl ⟨ p.1, hp, rfl ⟩

/-! ## Dependency- and peer-relation retraction -/

private theorem tryGranularN_intermediateN (n : N) (v : V) (m : N) :
    hcnm.tryGranularN (hcnm.intermediateN n v m) = none := by
  cases h : hcnm.tryGranularN (hcnm.intermediateN n v m) with
  | none => rfl
  | some p =>
    exact (hcnm.granularN_ne_intermediateN _ _ _ _ _ (hcnm.tryGranularN_some _ _ h)).elim

private theorem tryIntermediateN_granularN (n : N) (gg : G) :
    hcnm.tryIntermediateN (hcnm.granularN n gg) = none := by
  cases h : hcnm.tryIntermediateN (hcnm.granularN n gg) with
  | none => rfl
  | some p =>
    exact (hcnm.intermediateN_ne_granularN _ _ _ _ _ (hcnm.tryIntermediateN_some _ _ h)).elim

/-- Membership in `peerDeps`, decomposed into its three edge families. -/
theorem mem_peerDeps_iff {Δ_C : DepRel N V} {Θ : PeerRel N V} {g : V → G}
    {e : Package N' V' × N' × Finset V'} :
    e ∈ peerDeps Δ_C Θ g ↔
      (∃ n v m vs, ((n, v), m, vs) ∈ Δ_C ∧
        e = ((hcnm.granularN n (g v), hcvr.origV v), hcnm.intermediateN n v m,
             vs.map hcvr.origV)) ∨
      (∃ n v m vs, ((n, v), m, vs) ∈ Δ_C ∧ ∃ u ∈ vs,
        e = ((hcnm.intermediateN n v m, hcvr.origV u), hcnm.granularN m (g u),
             {hcvr.origV u})) ∨
      (∃ n v o us, ((n, v), o, us) ∈ Δ_C ∧ ∃ u ∈ us, ∃ m ws, ((o, u), m, ws) ∈ Θ ∧
        (∃ ws', ((n, v), m, ws') ∈ Δ_C) ∧
        e = ((hcnm.intermediateN n v o, hcvr.origV u), hcnm.intermediateN n v m,
             ws.map hcvr.origV)) := by
  simp only [peerDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_filter, Prod.exists]
  constructor
  · rintro ((⟨n, v, m, vs, hmem, rfl⟩ | ⟨n, v, m, vs, hmem, u, hu, rfl⟩) |
      ⟨n, v, o, us, hmem, u, hu, o', u', m, ws, ⟨hΘ, hpe⟩, hif⟩)
    · exact Or.inl ⟨n, v, m, vs, hmem, rfl⟩
    · exact Or.inr (Or.inl ⟨n, v, m, vs, hmem, u, hu, rfl⟩)
    · rw [hpe] at hΘ
      split at hif
      · rename_i hg
        rw [Finset.mem_singleton] at hif
        rw [Finset.filter_nonempty_iff] at hg
        obtain ⟨⟨xp, xm, xws⟩, hxmem, hx1, hx2⟩ := hg
        simp only at hx1 hx2
        rw [hx1, hx2] at hxmem
        exact Or.inr (Or.inr ⟨n, v, o, us, hmem, u, hu, m, ws, hΘ, ⟨xws, hxmem⟩, hif⟩)
      · exact absurd hif (Finset.notMem_empty e)
  · rintro (⟨n, v, m, vs, hmem, rfl⟩ | ⟨n, v, m, vs, hmem, u, hu, rfl⟩ |
      ⟨n, v, o, us, hmem, u, hu, m, ws, hΘ, ⟨ws', hws'⟩, rfl⟩)
    · exact Or.inl (Or.inl ⟨n, v, m, vs, hmem, rfl⟩)
    · exact Or.inl (Or.inr ⟨n, v, m, vs, hmem, u, hu, rfl⟩)
    · refine Or.inr ⟨n, v, o, us, hmem, u, hu, o, u, m, ws, ⟨hΘ, rfl⟩, ?_⟩
      rw [if_pos (Finset.filter_nonempty_iff.mpr ⟨((n, v), m, ws'), hws', rfl, rfl⟩)]
      exact Finset.mem_singleton.mpr rfl

/-- `tryInvDelta` inverts a depender→intermediate edge to its dependency. -/
private theorem tryInvDelta_eval {g : V → G} {n : N} {v : V} {m : N} {vs : Finset V} :
    tryInvDelta g ((hcnm.granularN n (g v), hcvr.origV v), hcnm.intermediateN n v m,
      vs.map hcvr.origV) = some ((n, v), m, vs) := by
  rw [tryInvDelta]
  simp only [hcnm.tryGranularN_granularN, hcvr.tryOrigV_origV,
    hcnm.tryIntermediateN_intermediateN, Concurrent.decodeVS_map_origV, and_self, if_true]

/-- `tryInvPeer` inverts an intermediate→intermediate edge to its peer constraint. -/
private theorem tryInvPeer_eval {g : V → G} {n : N} {v : V} {o : N} {u : V} {m : N}
    {ws : Finset V} :
    tryInvPeer g ((hcnm.intermediateN n v o, hcvr.origV u), hcnm.intermediateN n v m,
      ws.map hcvr.origV) = some ((o, u), m, ws) := by
  rw [tryInvPeer]
  simp only [hcnm.tryIntermediateN_intermediateN, hcvr.tryOrigV_origV,
    Concurrent.decodeVS_map_origV, and_self, if_true]

/-- Only depender→intermediate edges are inverted by `tryInvDelta`, to genuine
dependencies of `Δ_C`. -/
private theorem sound_delta {Δ_C : DepRel N V} {Θ : PeerRel N V} {g : V → G}
    {e : Package N' V' × N' × Finset V'} {d : Package N V × N × Finset V}
    (hmem : e ∈ peerDeps Δ_C Θ g) (h : tryInvDelta g e = some d) : d ∈ Δ_C := by
  rw [mem_peerDeps_iff] at hmem
  rcases hmem with ⟨n, v, m, vs, hmem, rfl⟩ | ⟨n, v, m, vs, hmem, u, hu, rfl⟩ |
    ⟨n, v, o, us, hmem, u, hu, m, ws, hΘ, hg, rfl⟩
  · rw [tryInvDelta_eval] at h; obtain rfl := Option.some.inj h; exact hmem
  · simp only [tryInvDelta, tryGranularN_intermediateN] at h; exact absurd h (by simp)
  · simp only [tryInvDelta, tryGranularN_intermediateN] at h; exact absurd h (by simp)

/-- Only intermediate→intermediate edges are inverted by `tryInvPeer`, to genuine
peer constraints of `Θ`. -/
private theorem sound_peer {Δ_C : DepRel N V} {Θ : PeerRel N V} {g : V → G}
    {e : Package N' V' × N' × Finset V'} {d : Package N V × N × Finset V}
    (hmem : e ∈ peerDeps Δ_C Θ g) (h : tryInvPeer g e = some d) : d ∈ Θ := by
  rw [mem_peerDeps_iff] at hmem
  rcases hmem with ⟨n, v, m, vs, hmem, rfl⟩ | ⟨n, v, m, vs, hmem, u, hu, rfl⟩ |
    ⟨n, v, o, us, hmem, u, hu, m, ws, hΘ, hg, rfl⟩
  · simp only [tryInvPeer, tryIntermediateN_granularN] at h; exact absurd h (by simp)
  · simp only [tryInvPeer, hcnm.tryIntermediateN_intermediateN, hcvr.tryOrigV_origV,
      tryIntermediateN_granularN] at h
    exact absurd h (by simp)
  · rw [tryInvPeer_eval] at h; obtain rfl := Option.some.inj h; exact hΘ

/-- **Instance-level retraction for the peer dependency relation.** The core
dependency component is recovered edge-locally, with no side-condition. -/
theorem liftDeps_peerDeps (Δ_C : DepRel N V) (Θ : PeerRel N V) (g : V → G) :
    liftDeps g (peerDeps Δ_C Θ g) = Δ_C := by
  ext d
  simp only [liftDeps, Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def]
  constructor
  · rintro ⟨e, he, hd⟩; exact sound_delta he hd
  · intro hd
    obtain ⟨⟨n, v⟩, m, vs⟩ := d
    exact ⟨_, mem_peerDeps_iff.mpr (Or.inl ⟨n, v, m, vs, hd, rfl⟩), tryInvDelta_eval⟩

/-- **Instance-level retraction for the peer relation.** Recovering `Θ` requires
it to be `GroundedIn Δ_C`: peer constraints with no activating parent dependency
leave no trace in the reduction and cannot be lifted back. -/
theorem liftPeer_peerDeps (Δ_C : DepRel N V) (Θ : PeerRel N V) (g : V → G)
    (hground : Θ.GroundedIn Δ_C) :
    liftPeer g (peerDeps Δ_C Θ g) = Θ := by
  ext d
  simp only [liftPeer, Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def]
  constructor
  · rintro ⟨e, he, hd⟩; exact sound_peer he hd
  · intro hd
    obtain ⟨⟨o, u⟩, m, ws⟩ := d
    obtain ⟨n, v, us, hno, hu, ws', hnm⟩ := hground o u m ws hd
    exact ⟨_, mem_peerDeps_iff.mpr
      (Or.inr (Or.inr ⟨n, v, o, us, hno, u, hu, m, ws, hd, ⟨ws', hnm⟩, rfl⟩)), tryInvPeer_eval⟩

/-- **Full instance-level retraction for the peer-dependency extension.** For a
`GroundedIn` peer relation, lifting the reduced package universe, dependency
relation, and peer relation recovers the original triple `(R_C, Δ_C, Θ)`. -/
theorem peerLift_peerReduce (R_C : Real N V) (Δ_C : DepRel N V) (Θ : PeerRel N V) (g : V → G)
    (hground : Θ.GroundedIn Δ_C) :
    (liftReal g (peerReal (N' := N') (V' := V') R_C Δ_C Θ g),
     liftDeps g (peerDeps (N' := N') (V' := V') Δ_C Θ g),
     liftPeer g (peerDeps (N' := N') (V' := V') Δ_C Θ g)) = (R_C, Δ_C, Θ) := by
  rw [liftReal_peerReal, liftDeps_peerDeps, liftPeer_peerDeps _ _ _ hground]

end PackageCalculus.PeerDep