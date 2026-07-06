import PackageCalculus.Extensions.PackageFormula.Lifting.Definition

namespace PackageCalculus.PkgFormula

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hpn : HasPFNames N V N'] [hpv : Conflict.HasConflictVersions V V']

/-! ## Round-trip theorems -/

theorem liftReal_pfReal (R : Real N V) (Δ_Ψ : PFDepRel N V) :
    liftReal (pfReal R Δ_Ψ) = R := by
  ext p
  simp only [mem_liftReal, pfReal, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion]
  constructor
  · intro h
    rcases h with ⟨q, hqR, heq⟩ | ⟨a, haΔ, hmem⟩
    · simp only [embedPkg, Prod.mk.injEq] at heq
      have h1 := hpn.origN.injective heq.1; have h2 := hpv.origV.injective heq.2
      exact (Prod.ext h1 h2 : q = p) ▸ hqR
    · exfalso
      exact witnessPackages_not_orig (embedPkg a.1) a.2 p.1 (hpv.origV p.2) hmem
  · intro hp
    exact Or.inl ⟨p, hp, rfl⟩

/-! ## Atom-set retraction

The encoding erases conjunction structure and entry boundaries, so neither
`Δ_Ψ` nor its per-entry NNF is recoverable. What is recoverable — exactly —
is each depender's set of NNF atoms (`liftAtoms_pfDeps`). -/

/-! ### Decoder disjointness -/

private theorem tryOrigN_syntheticN (n : N) (vs : Finset V) :
    hpn.tryOrigN (hpn.syntheticN n vs) = none := by
  cases h : hpn.tryOrigN (hpn.syntheticN n vs) with
  | none => rfl
  | some m => exact (hpn.origN_ne_syntheticN _ _ _ (hpn.tryOrigN_some _ _ h)).elim

private theorem tryOrigN_disjunctN (ψ₁ ψ₂ : Formula N V) :
    hpn.tryOrigN (hpn.disjunctN ψ₁ ψ₂) = none := by
  cases h : hpn.tryOrigN (hpn.disjunctN ψ₁ ψ₂) with
  | none => rfl
  | some m => exact (hpn.origN_ne_disjunctN _ _ _ (hpn.tryOrigN_some _ _ h)).elim

private theorem trySyntheticN_origN (n : N) :
    hpn.trySyntheticN (hpn.origN n) = none := by
  cases h : hpn.trySyntheticN (hpn.origN n) with
  | none => rfl
  | some q => exact (hpn.syntheticN_ne_origN _ _ _ (hpn.trySyntheticN_some _ _ h)).elim

private theorem trySyntheticN_disjunctN (ψ₁ ψ₂ : Formula N V) :
    hpn.trySyntheticN (hpn.disjunctN ψ₁ ψ₂) = none := by
  cases h : hpn.trySyntheticN (hpn.disjunctN ψ₁ ψ₂) with
  | none => rfl
  | some q => exact (hpn.syntheticN_ne_disjunctN _ _ _ _ (hpn.trySyntheticN_some _ _ h)).elim

private theorem tryDisjunctN_origN (n : N) :
    hpn.tryDisjunctN (hpn.origN n) = none := by
  cases h : hpn.tryDisjunctN (hpn.origN n) with
  | none => rfl
  | some q => exact (hpn.disjunctN_ne_origN _ _ _ (hpn.tryDisjunctN_some _ _ h)).elim

private theorem tryDisjunctN_syntheticN (n : N) (vs : Finset V) :
    hpn.tryDisjunctN (hpn.syntheticN n vs) = none := by
  cases h : hpn.tryDisjunctN (hpn.syntheticN n vs) with
  | none => rfl
  | some q => exact (hpn.disjunctN_ne_syntheticN _ _ _ _ (hpn.tryDisjunctN_some _ _ h)).elim

/-! ### Decoder evaluation and rejection on the edge families -/

private theorem tryInvPos_eval (a : N) (b : V) (n : N) (vs : Finset V) :
    tryInvPos ((hpn.origN a, hpv.origV b), hpn.origN n, embedVS (hpv := hpv) vs) =
      some ((a, b), .pos n vs) := by
  simp only [tryInvPos, hpn.tryOrigN_origN, hpv.tryOrigV_origV, decodeVS_embedVS, if_true]

private theorem tryInvNeg_eval (a : N) (b : V) (n : N) (vs : Finset V) :
    tryInvNeg ((hpn.origN a, hpv.origV b), hpn.syntheticN n vs, ({hpv.oneV} : Finset V')) =
      some ((a, b), .neg n vs) := by
  simp only [tryInvNeg, hpn.tryOrigN_origN, hpv.tryOrigV_origV,
    hpn.trySyntheticN_syntheticN, if_true]

private theorem tryInvDisj_eval (a : N) (b : V) (ψ₁ ψ₂ : Formula N V) :
    tryInvDisj ((hpn.origN a, hpv.origV b), hpn.disjunctN ψ₁ ψ₂,
      ({hpv.zeroV, hpv.oneV} : Finset V')) = some ((a, b), .disj ψ₁ ψ₂) := by
  simp only [tryInvDisj, hpn.tryOrigN_origN, hpv.tryOrigV_origV,
    hpn.tryDisjunctN_disjunctN, if_true]

private theorem tryInvNeg_posEdge (a : N) (b : V) (n : N) (ws : Finset V') :
    tryInvNeg (hpn := hpn) ((hpn.origN a, hpv.origV b), hpn.origN n, ws) = none := by
  simp only [tryInvNeg, hpn.tryOrigN_origN, hpv.tryOrigV_origV, trySyntheticN_origN]

private theorem tryInvDisj_posEdge (a : N) (b : V) (n : N) (ws : Finset V') :
    tryInvDisj (hpn := hpn) ((hpn.origN a, hpv.origV b), hpn.origN n, ws) = none := by
  simp only [tryInvDisj, hpn.tryOrigN_origN, hpv.tryOrigV_origV, tryDisjunctN_origN]

private theorem tryInvPos_negEdge (a : N) (b : V) (n : N) (vs : Finset V) (ws : Finset V') :
    tryInvPos (hpn := hpn) ((hpn.origN a, hpv.origV b), hpn.syntheticN n vs, ws) = none := by
  simp only [tryInvPos, hpn.tryOrigN_origN, hpv.tryOrigV_origV, tryOrigN_syntheticN]

private theorem tryInvDisj_negEdge (a : N) (b : V) (n : N) (vs : Finset V) (ws : Finset V') :
    tryInvDisj (hpn := hpn) ((hpn.origN a, hpv.origV b), hpn.syntheticN n vs, ws) = none := by
  simp only [tryInvDisj, hpn.tryOrigN_origN, hpv.tryOrigV_origV, tryDisjunctN_syntheticN]

/-- The negative-literal guard edges carry version `{0}`, not `{1}`. -/
private theorem tryInvNeg_guard (a : N) (b : V) (n : N) (vs : Finset V) :
    tryInvNeg (hpn := hpn) ((hpn.origN a, hpv.origV b), hpn.syntheticN n vs,
      ({hpv.zeroV} : Finset V')) = none := by
  simp only [tryInvNeg, hpn.tryOrigN_origN, hpv.tryOrigV_origV, hpn.trySyntheticN_syntheticN,
    Finset.singleton_inj]
  rw [if_neg hpv.zeroV_ne_oneV]

private theorem tryInvPos_disjEdge (a : N) (b : V) (ψ₁ ψ₂ : Formula N V) (ws : Finset V') :
    tryInvPos (hpn := hpn) ((hpn.origN a, hpv.origV b), hpn.disjunctN ψ₁ ψ₂, ws) = none := by
  simp only [tryInvPos, hpn.tryOrigN_origN, hpv.tryOrigV_origV, tryOrigN_disjunctN]

private theorem tryInvNeg_disjEdge (a : N) (b : V) (ψ₁ ψ₂ : Formula N V) (ws : Finset V') :
    tryInvNeg (hpn := hpn) ((hpn.origN a, hpv.origV b), hpn.disjunctN ψ₁ ψ₂, ws) = none := by
  simp only [tryInvNeg, hpn.tryOrigN_origN, hpv.tryOrigV_origV, trySyntheticN_disjunctN]

private theorem tryInvPos_nested (ψ₁ ψ₂ : Formula N V) (b : V') (r : N' × Finset V') :
    tryInvPos (hpn := hpn) ((hpn.disjunctN ψ₁ ψ₂, b), r) = none := by
  simp only [tryInvPos, tryOrigN_disjunctN]

private theorem tryInvNeg_nested (ψ₁ ψ₂ : Formula N V) (b : V') (r : N' × Finset V') :
    tryInvNeg (hpn := hpn) ((hpn.disjunctN ψ₁ ψ₂, b), r) = none := by
  simp only [tryInvNeg, tryOrigN_disjunctN]

private theorem tryInvDisj_nested (ψ₁ ψ₂ : Formula N V) (b : V') (r : N' × Finset V') :
    tryInvDisj (hpn := hpn) ((hpn.disjunctN ψ₁ ψ₂, b), r) = none := by
  simp only [tryInvDisj, tryOrigN_disjunctN]

/-! ### Structure of the encoding's edge set -/

/-- Every atom of `ψ` contributes its edge to the encoding. -/
private theorem atomEdge_mem (k : ℕ) :
    ∀ ψ : Formula N V, ψ.weight ≤ k → ∀ (q : Package N' V') (a : Atom N V),
      a ∈ atoms ψ → atomEdge q a ∈ encodeNNF q ψ := by
  induction k with
  | zero =>
    intro ψ hw q a ha
    cases ψ with
    | dep n vs =>
      simp only [atoms, Finset.mem_singleton] at ha
      subst ha
      simp only [encodeNNF, atomEdge, Finset.mem_singleton]
    | conj ψL ψR => simp only [Formula.weight] at hw; omega
    | disj ψL ψR => simp only [Formula.weight] at hw; omega
    | neg ψ₀ => simp only [Formula.weight] at hw; omega
  | succ k ih =>
    intro ψ hw q a ha
    cases ψ with
    | dep n vs =>
      simp only [atoms, Finset.mem_singleton] at ha
      subst ha
      simp only [encodeNNF, atomEdge, Finset.mem_singleton]
    | conj ψL ψR =>
      simp only [atoms, Finset.mem_union] at ha
      simp only [Formula.weight] at hw
      simp only [encodeNNF, Finset.mem_union]
      rcases ha with ha | ha
      · exact Or.inl (ih ψL (by omega) q a ha)
      · exact Or.inr (ih ψR (by omega) q a ha)
    | disj ψL ψR =>
      simp only [atoms, Finset.mem_singleton] at ha
      subst ha
      simp only [encodeNNF, atomEdge, Finset.mem_union, Finset.mem_singleton]
      exact Or.inl (Or.inl trivial)
    | neg ψ₀ =>
      cases ψ₀ with
      | dep n vs =>
        simp only [atoms, Finset.mem_singleton] at ha
        subst ha
        simp only [encodeNNF, atomEdge, Finset.mem_union, Finset.mem_singleton]
        exact Or.inl trivial
      | conj ψL ψR =>
        simp only [Formula.weight] at hw
        have ha' : a ∈ atoms (Formula.disj (.neg ψL) (.neg ψR)) := by
          simpa only [atoms] using ha
        have h := ih (Formula.disj (.neg ψL) (.neg ψR))
          (by simp only [Formula.weight]; omega) q a ha'
        simpa only [encodeNNF] using h
      | disj ψL ψR =>
        simp only [Formula.weight] at hw
        have ha' : a ∈ atoms (Formula.conj (.neg ψL) (.neg ψR)) := by
          simpa only [atoms] using ha
        have h := ih (Formula.conj (.neg ψL) (.neg ψR))
          (by simp only [Formula.weight]; omega) q a ha'
        simpa only [encodeNNF] using h
      | neg ψ₁ =>
        simp only [Formula.weight] at hw
        have ha' : a ∈ atoms ψ₁ := by simpa only [atoms] using ha
        have h := ih ψ₁ (by omega) q a ha'
        simpa only [encodeNNF] using h

/-- Every edge of the encoding is a top-level atom edge, a nested edge (its
depender bears a disjunct-witness name), or a negative-literal guard edge. -/
private theorem encodeNNF_cases (k : ℕ) :
    ∀ ψ : Formula N V, ψ.weight ≤ k → ∀ (q : Package N' V') e, e ∈ encodeNNF q ψ →
      (∃ a ∈ atoms ψ, e = atomEdge q a) ∨
      (∃ (φ₁ φ₂ : Formula N V) (b : V'), e.1 = (hpn.disjunctN φ₁ φ₂, b)) ∨
      (∃ n vs u, u ∈ vs ∧
        e = ((hpn.origN n, hpv.origV u), hpn.syntheticN n vs, ({hpv.zeroV} : Finset V'))) := by
  induction k with
  | zero =>
    intro ψ hw q e he
    cases ψ with
    | dep n vs =>
      simp only [encodeNNF, Finset.mem_singleton] at he
      exact Or.inl ⟨.pos n vs, by simp [atoms], by rw [he]; rfl⟩
    | conj ψL ψR => simp only [Formula.weight] at hw; omega
    | disj ψL ψR => simp only [Formula.weight] at hw; omega
    | neg ψ₀ => simp only [Formula.weight] at hw; omega
  | succ k ih =>
    intro ψ hw q e he
    cases ψ with
    | dep n vs =>
      simp only [encodeNNF, Finset.mem_singleton] at he
      exact Or.inl ⟨.pos n vs, by simp [atoms], by rw [he]; rfl⟩
    | conj ψL ψR =>
      simp only [Formula.weight] at hw
      simp only [encodeNNF, Finset.mem_union] at he
      rcases he with he | he
      · rcases ih ψL (by omega) q e he with ⟨a, ha, rfl⟩ | h | h
        · exact Or.inl ⟨a, by simp only [atoms, Finset.mem_union]; exact Or.inl ha, rfl⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases ih ψR (by omega) q e he with ⟨a, ha, rfl⟩ | h | h
        · exact Or.inl ⟨a, by simp only [atoms, Finset.mem_union]; exact Or.inr ha, rfl⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    | disj ψL ψR =>
      simp only [Formula.weight] at hw
      simp only [encodeNNF, Finset.mem_union, Finset.mem_singleton] at he
      rcases he with (he | he) | he
      · exact Or.inl ⟨.disj ψL ψR, by simp [atoms], by rw [he]; rfl⟩
      · rcases ih ψL (by omega) _ e he with ⟨a, _, rfl⟩ | h | h
        · exact Or.inr (Or.inl ⟨ψL, ψR, hpv.zeroV, atomEdge_fst _ a⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases ih ψR (by omega) _ e he with ⟨a, _, rfl⟩ | h | h
        · exact Or.inr (Or.inl ⟨ψL, ψR, hpv.oneV, atomEdge_fst _ a⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    | neg ψ₀ =>
      cases ψ₀ with
      | dep n vs =>
        simp only [encodeNNF, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at he
        rcases he with he | ⟨u, hu, heq⟩
        · exact Or.inl ⟨.neg n vs, by simp [atoms], by rw [he]; rfl⟩
        · exact Or.inr (Or.inr ⟨n, vs, u, hu, heq.symm⟩)
      | conj ψL ψR =>
        simp only [Formula.weight] at hw
        have he' : e ∈ encodeNNF q (Formula.disj (.neg ψL) (.neg ψR)) := by
          simpa only [encodeNNF] using he
        rcases ih (Formula.disj (.neg ψL) (.neg ψR))
            (by simp only [Formula.weight]; omega) q e he' with ⟨a, ha, rfl⟩ | h | h
        · exact Or.inl ⟨a, by simpa only [atoms] using ha, rfl⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      | disj ψL ψR =>
        simp only [Formula.weight] at hw
        have he' : e ∈ encodeNNF q (Formula.conj (.neg ψL) (.neg ψR)) := by
          simpa only [encodeNNF] using he
        rcases ih (Formula.conj (.neg ψL) (.neg ψR))
            (by simp only [Formula.weight]; omega) q e he' with ⟨a, ha, rfl⟩ | h | h
        · exact Or.inl ⟨a, by simpa only [atoms] using ha, rfl⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      | neg ψ₁ =>
        simp only [Formula.weight] at hw
        have he' : e ∈ encodeNNF q ψ₁ := by simpa only [encodeNNF] using he
        rcases ih ψ₁ (by omega) q e he' with ⟨a, ha, rfl⟩ | h | h
        · exact Or.inl ⟨a, by simpa only [atoms] using ha, rfl⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

/-! ### The atom-set retraction -/

/-- **Atom-set retraction for package formulae.** The reduction erases
conjunction structure and entry boundaries, but preserves — exactly — each
depender's set of NNF atoms: lifting the reduced dependency relation recovers
the per-depender union of the atom sets of its formulae. No side-conditions
are required; merging is built into the right-hand side. -/
theorem liftAtoms_pfDeps (Δ_Ψ : PFDepRel N V) :
    liftAtoms (pfDeps (N' := N') (V' := V') Δ_Ψ) =
      Δ_Ψ.biUnion (fun pψ => (atoms pψ.2).image (fun a => (pψ.1, a))) := by
  ext d
  simp only [liftAtoms, Finset.mem_biUnion, Finset.mem_union, Option.mem_toFinset,
    Option.mem_def, Finset.mem_image]
  constructor
  · rintro ⟨e, he, hdec⟩
    simp only [pfDeps, encode, Finset.mem_biUnion, Prod.exists] at he
    obtain ⟨p₁, p₂, ψ, hmem, hin⟩ := he
    rcases encodeNNF_cases ψ.weight ψ le_rfl _ e hin with ⟨a, ha, rfl⟩ |
      ⟨φ₁, φ₂, b, hfst⟩ | ⟨n, vs, u, hu, rfl⟩
    · cases a with
      | pos n vs =>
        simp only [atomEdge, embedPkg] at hdec
        rw [tryInvPos_eval, tryInvNeg_posEdge, tryInvDisj_posEdge] at hdec
        rcases hdec with (hd | hd) | hd
        · obtain rfl := Option.some.inj hd
          exact ⟨((p₁, p₂), ψ), hmem, .pos n vs, ha, rfl⟩
        · exact absurd hd (by simp)
        · exact absurd hd (by simp)
      | neg n vs =>
        simp only [atomEdge, embedPkg] at hdec
        rw [tryInvPos_negEdge, tryInvNeg_eval, tryInvDisj_negEdge] at hdec
        rcases hdec with (hd | hd) | hd
        · exact absurd hd (by simp)
        · obtain rfl := Option.some.inj hd
          exact ⟨((p₁, p₂), ψ), hmem, .neg n vs, ha, rfl⟩
        · exact absurd hd (by simp)
      | disj ψ₁ ψ₂ =>
        simp only [atomEdge, embedPkg] at hdec
        rw [tryInvPos_disjEdge, tryInvNeg_disjEdge, tryInvDisj_eval] at hdec
        rcases hdec with (hd | hd) | hd
        · exact absurd hd (by simp)
        · exact absurd hd (by simp)
        · obtain rfl := Option.some.inj hd
          exact ⟨((p₁, p₂), ψ), hmem, .disj ψ₁ ψ₂, ha, rfl⟩
    · obtain ⟨e1, e2⟩ := e
      subst hfst
      rw [tryInvPos_nested, tryInvNeg_nested, tryInvDisj_nested] at hdec
      rcases hdec with (hd | hd) | hd <;> exact absurd hd (by simp)
    · rw [tryInvPos_negEdge, tryInvNeg_guard, tryInvDisj_negEdge] at hdec
      rcases hdec with (hd | hd) | hd <;> exact absurd hd (by simp)
  · rintro ⟨⟨⟨p₁, p₂⟩, ψ⟩, hmem, a, ha, rfl⟩
    refine ⟨atomEdge (embedPkg (p₁, p₂)) a, ?_, ?_⟩
    · simp only [pfDeps, encode, Finset.mem_biUnion, Prod.exists]
      exact ⟨p₁, p₂, ψ, hmem, atomEdge_mem ψ.weight ψ le_rfl _ a ha⟩
    · cases a with
      | pos n vs =>
        simp only [atomEdge, embedPkg]
        rw [tryInvPos_eval]
        exact Or.inl (Or.inl rfl)
      | neg n vs =>
        simp only [atomEdge, embedPkg]
        rw [tryInvNeg_eval]
        exact Or.inl (Or.inr rfl)
      | disj ψ₁ ψ₂ =>
        simp only [atomEdge, embedPkg]
        rw [tryInvDisj_eval]
        exact Or.inr rfl

/-! ### The atom set is a faithful normal form -/

private theorem satisfies_iff_atoms_aux (k : ℕ) :
    ∀ ψ : Formula N V, ψ.weight ≤ k → ∀ S : Finset (Package N V),
      (S ⊨ ψ) ↔ ∀ a ∈ atoms ψ, S ⊨ a.toFormula := by
  induction k with
  | zero =>
    intro ψ hw S
    cases ψ with
    | dep n vs => simp [atoms, Atom.toFormula]
    | conj ψL ψR => simp only [Formula.weight] at hw; omega
    | disj ψL ψR => simp only [Formula.weight] at hw; omega
    | neg ψ₀ => simp only [Formula.weight] at hw; omega
  | succ k ih =>
    intro ψ hw S
    cases ψ with
    | dep n vs => simp [atoms, Atom.toFormula]
    | conj ψL ψR =>
      simp only [Formula.weight] at hw
      simp only [Formula.satisfies, atoms, Finset.mem_union]
      rw [ih ψL (by omega) S, ih ψR (by omega) S]
      constructor
      · rintro ⟨hL, hR⟩ a (ha | ha)
        · exact hL a ha
        · exact hR a ha
      · intro h
        exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
    | disj ψL ψR => simp [atoms, Atom.toFormula]
    | neg ψ₀ =>
      cases ψ₀ with
      | dep n vs => simp [atoms, Atom.toFormula]
      | conj ψL ψR =>
        simp only [atoms, Atom.toFormula, Finset.mem_singleton, forall_eq]
        simp only [Formula.satisfies]
        exact not_and_or
      | disj ψL ψR =>
        simp only [Formula.weight] at hw
        have hL := ih (Formula.neg ψL) (by simp only [Formula.weight]; omega) S
        have hR := ih (Formula.neg ψR) (by simp only [Formula.weight]; omega) S
        simp only [Formula.satisfies] at hL hR
        simp only [atoms, Finset.mem_union, Formula.satisfies, not_or]
        constructor
        · rintro ⟨hnl, hnr⟩ a (ha | ha)
          · exact (hL.mp hnl) a ha
          · exact (hR.mp hnr) a ha
        · intro h
          exact ⟨hL.mpr (fun a ha => h a (Or.inl ha)), hR.mpr (fun a ha => h a (Or.inr ha))⟩
      | neg ψ₁ =>
        simp only [Formula.weight] at hw
        have h := ih ψ₁ (by omega) S
        simp only [atoms, Formula.satisfies, not_not]
        exact h

/-- The atom set is a faithful normal form: a resolution satisfies a formula
iff it satisfies every one of its NNF atoms. -/
theorem satisfies_iff_atoms (S : Finset (Package N V)) (ψ : Formula N V) :
    (S ⊨ ψ) ↔ ∀ a ∈ atoms ψ, S ⊨ a.toFormula :=
  satisfies_iff_atoms_aux ψ.weight ψ le_rfl S

end PackageCalculus.PkgFormula
