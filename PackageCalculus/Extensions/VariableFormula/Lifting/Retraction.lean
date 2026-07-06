import PackageCalculus.Extensions.VariableFormula.Lifting.Definition

namespace PackageCalculus.VarFormula

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {X : Type*} [DecidableEq X] {Y : Type*} [DecidableEq Y]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVFNames N V X Y N'] [hvv : HasVFVersions V Y V']

/-! ## Round-trip theorems -/

theorem liftReal_vfReal [LT Y] [DecidableRel (· < · : Y → Y → Prop)] [Fintype X]
    (Y_x : X → Finset Y) (R : Real N V) (Δ_Ψ : VFDepRel N V X Y) :
    liftReal (X := X) (Y := Y) (vfReal (N' := N') (V' := V') Y_x R Δ_Ψ) = R := by
  ext p;
  convert mem_liftReal;
  unfold vfReal;
  simp +decide [ embedPkg ];
  exact fun _ _ _ _ h => False.elim ( witnessPackages_not_orig' _ _ _ _ h )

/-! ## Atom-set retraction

As for package formulae, the encoding erases conjunction structure and entry
boundaries; additionally a variable comparison survives only as its extension
over the declared domain. What is recoverable — exactly — is each depender's
set of NNF atoms with variable atoms so normalised (`liftAtoms_vfDeps`). -/

set_option linter.unusedSectionVars false

/-! ### Decoder disjointness -/

private theorem tryOrigN_syntheticN (n : N) (vs : Finset V) :
    hvn.tryOrigN (hvn.syntheticN n vs) = none := by
  cases h : hvn.tryOrigN (hvn.syntheticN n vs) with
  | none => rfl
  | some m => exact (hvn.origN_ne_syntheticN _ _ _ (hvn.tryOrigN_some _ _ h)).elim

private theorem tryOrigN_disjunctN (ψ₁ ψ₂ : Formula N V X Y) :
    hvn.tryOrigN (hvn.disjunctN ψ₁ ψ₂) = none := by
  cases h : hvn.tryOrigN (hvn.disjunctN ψ₁ ψ₂) with
  | none => rfl
  | some m => exact (hvn.origN_ne_disjunctN _ _ _ (hvn.tryOrigN_some _ _ h)).elim

private theorem tryOrigN_varN (x : X) :
    hvn.tryOrigN (hvn.varN (V := V) x) = none := by
  cases h : hvn.tryOrigN (hvn.varN (V := V) x) with
  | none => rfl
  | some m => exact (hvn.origN_ne_varN _ _ (hvn.tryOrigN_some _ _ h)).elim

private theorem trySyntheticN_origN (n : N) :
    hvn.trySyntheticN (V := V) (hvn.origN n) = none := by
  cases h : hvn.trySyntheticN (V := V) (hvn.origN n) with
  | none => rfl
  | some q => exact (hvn.syntheticN_ne_origN _ _ _ (hvn.trySyntheticN_some _ _ h)).elim

private theorem trySyntheticN_disjunctN (ψ₁ ψ₂ : Formula N V X Y) :
    hvn.trySyntheticN (hvn.disjunctN ψ₁ ψ₂) = none := by
  cases h : hvn.trySyntheticN (hvn.disjunctN ψ₁ ψ₂) with
  | none => rfl
  | some q => exact (hvn.syntheticN_ne_disjunctN _ _ _ _ (hvn.trySyntheticN_some _ _ h)).elim

private theorem trySyntheticN_varN (x : X) :
    hvn.trySyntheticN (V := V) (hvn.varN (V := V) x) = none := by
  cases h : hvn.trySyntheticN (V := V) (hvn.varN (V := V) x) with
  | none => rfl
  | some q => exact (hvn.syntheticN_ne_varN _ _ _ (hvn.trySyntheticN_some _ _ h)).elim

private theorem tryDisjunctN_origN (n : N) :
    hvn.tryDisjunctN (X := X) (Y := Y) (hvn.origN n) = none := by
  cases h : hvn.tryDisjunctN (X := X) (Y := Y) (hvn.origN n) with
  | none => rfl
  | some q => exact (hvn.disjunctN_ne_origN _ _ _ (hvn.tryDisjunctN_some _ _ h)).elim

private theorem tryDisjunctN_syntheticN (n : N) (vs : Finset V) :
    hvn.tryDisjunctN (X := X) (Y := Y) (hvn.syntheticN n vs) = none := by
  cases h : hvn.tryDisjunctN (X := X) (Y := Y) (hvn.syntheticN n vs) with
  | none => rfl
  | some q => exact (hvn.disjunctN_ne_syntheticN _ _ _ _ (hvn.tryDisjunctN_some _ _ h)).elim

private theorem tryDisjunctN_varN (x : X) :
    hvn.tryDisjunctN (hvn.varN (V := V) x) = none := by
  cases h : hvn.tryDisjunctN (hvn.varN (V := V) x) with
  | none => rfl
  | some q => exact (hvn.disjunctN_ne_varN _ _ _ (hvn.tryDisjunctN_some _ _ h)).elim

private theorem tryVarN_origN (n : N) :
    hvn.tryVarN (V := V) (Y := Y) (hvn.origN n) = none := by
  cases h : hvn.tryVarN (V := V) (Y := Y) (hvn.origN n) with
  | none => rfl
  | some x => exact (hvn.varN_ne_origN _ _ (hvn.tryVarN_some _ _ h)).elim

private theorem tryVarN_syntheticN (n : N) (vs : Finset V) :
    hvn.tryVarN (Y := Y) (hvn.syntheticN n vs) = none := by
  cases h : hvn.tryVarN (Y := Y) (hvn.syntheticN n vs) with
  | none => rfl
  | some x => exact (hvn.varN_ne_syntheticN _ _ _ (hvn.tryVarN_some _ _ h)).elim

private theorem tryVarN_disjunctN (ψ₁ ψ₂ : Formula N V X Y) :
    hvn.tryVarN (hvn.disjunctN ψ₁ ψ₂) = none := by
  cases h : hvn.tryVarN (hvn.disjunctN ψ₁ ψ₂) with
  | none => rfl
  | some x => exact (hvn.varN_ne_disjunctN _ _ _ (hvn.tryVarN_some _ _ h)).elim

/-! ### Decoder evaluation and rejection on the edge families -/

private theorem tryInvPos_eval (a : N) (b : V) (n : N) (vs : Finset V) :
    tryInvPos (N := N) (V := V) (X := X) (Y := Y)
      ((hvn.origN a, hvv.origV b), hvn.origN n, vs.map hvv.origV) =
      some ((a, b), .pos n vs) := by
  simp only [tryInvPos, hvn.tryOrigN_origN, hvv.tryOrigV_origV, decodeVS_map_origV, if_true]

private theorem tryInvNeg_eval (a : N) (b : V) (n : N) (vs : Finset V) :
    tryInvNeg (N := N) (V := V) (X := X) (Y := Y)
      ((hvn.origN a, hvv.origV b), hvn.syntheticN n vs, ({hvv.oneV} : Finset V')) =
      some ((a, b), .neg n vs) := by
  simp only [tryInvNeg, hvn.tryOrigN_origN, hvv.tryOrigV_origV,
    hvn.trySyntheticN_syntheticN, if_true]

private theorem tryInvDisj_eval (a : N) (b : V) (ψ₁ ψ₂ : Formula N V X Y) :
    tryInvDisj ((hvn.origN a, hvv.origV b), hvn.disjunctN ψ₁ ψ₂,
      ({hvv.zeroV, hvv.oneV} : Finset V')) = some ((a, b), .disj ψ₁ ψ₂) := by
  simp only [tryInvDisj, hvn.tryOrigN_origN, hvv.tryOrigV_origV,
    hvn.tryDisjunctN_disjunctN, if_true]

private theorem tryInvVar_eval (a : N) (b : V) (x : X) (ys : Finset Y) :
    tryInvVar ((hvn.origN a, hvv.origV b), hvn.varN (V := V) x, ys.map hvv.varValV) =
      some ((a, b), .var x ys) := by
  simp only [tryInvVar, hvn.tryOrigN_origN, hvv.tryOrigV_origV, hvn.tryVarN_varN,
    decodeYS_map_varValV, if_true]

private theorem tryInvNeg_posEdge (a : N) (b : V) (n : N) (ws : Finset V') :
    tryInvNeg (N := N) (V := V) (X := X) (Y := Y) ((hvn.origN a, hvv.origV b), hvn.origN n, ws) = none := by
  simp only [tryInvNeg, hvn.tryOrigN_origN, hvv.tryOrigV_origV, trySyntheticN_origN]

private theorem tryInvDisj_posEdge (a : N) (b : V) (n : N) (ws : Finset V') :
    tryInvDisj (N := N) (V := V) (X := X) (Y := Y) ((hvn.origN a, hvv.origV b), hvn.origN n, ws) = none := by
  simp only [tryInvDisj, hvn.tryOrigN_origN, hvv.tryOrigV_origV, tryDisjunctN_origN]

private theorem tryInvVar_posEdge (a : N) (b : V) (n : N) (ws : Finset V') :
    tryInvVar (N := N) (V := V) (X := X) (Y := Y) ((hvn.origN a, hvv.origV b), hvn.origN n, ws) = none := by
  simp only [tryInvVar, hvn.tryOrigN_origN, hvv.tryOrigV_origV, tryVarN_origN]

private theorem tryInvPos_negEdge (a : N) (b : V) (n : N) (vs : Finset V) (ws : Finset V') :
    tryInvPos (N := N) (V := V) (X := X) (Y := Y)
      ((hvn.origN a, hvv.origV b), hvn.syntheticN n vs, ws) = none := by
  simp only [tryInvPos, hvn.tryOrigN_origN, hvv.tryOrigV_origV, tryOrigN_syntheticN]

private theorem tryInvDisj_negEdge (a : N) (b : V) (n : N) (vs : Finset V) (ws : Finset V') :
    tryInvDisj (N := N) (V := V) (X := X) (Y := Y)
      ((hvn.origN a, hvv.origV b), hvn.syntheticN n vs, ws) = none := by
  simp only [tryInvDisj, hvn.tryOrigN_origN, hvv.tryOrigV_origV, tryDisjunctN_syntheticN]

private theorem tryInvVar_negEdge (a : N) (b : V) (n : N) (vs : Finset V) (ws : Finset V') :
    tryInvVar (N := N) (V := V) (X := X) (Y := Y)
      ((hvn.origN a, hvv.origV b), hvn.syntheticN n vs, ws) = none := by
  simp only [tryInvVar, hvn.tryOrigN_origN, hvv.tryOrigV_origV, tryVarN_syntheticN]

/-- The negative-literal guard edges carry version `{0}`, not `{1}`. -/
private theorem tryInvNeg_guard (a : N) (b : V) (n : N) (vs : Finset V) :
    tryInvNeg (N := N) (V := V) (X := X) (Y := Y) ((hvn.origN a, hvv.origV b), hvn.syntheticN n vs,
      ({hvv.zeroV} : Finset V')) = none := by
  simp only [tryInvNeg, hvn.tryOrigN_origN, hvv.tryOrigV_origV, hvn.trySyntheticN_syntheticN,
    Finset.singleton_inj]
  rw [if_neg hvv.zeroV_ne_oneV]

private theorem tryInvPos_disjEdge (a : N) (b : V) (ψ₁ ψ₂ : Formula N V X Y) (ws : Finset V') :
    tryInvPos (N := N) (V := V) (X := X) (Y := Y) ((hvn.origN a, hvv.origV b), hvn.disjunctN ψ₁ ψ₂, ws) = none := by
  simp only [tryInvPos, hvn.tryOrigN_origN, hvv.tryOrigV_origV, tryOrigN_disjunctN]

private theorem tryInvNeg_disjEdge (a : N) (b : V) (ψ₁ ψ₂ : Formula N V X Y) (ws : Finset V') :
    tryInvNeg (N := N) (V := V) (X := X) (Y := Y) ((hvn.origN a, hvv.origV b), hvn.disjunctN ψ₁ ψ₂, ws) = none := by
  simp only [tryInvNeg, hvn.tryOrigN_origN, hvv.tryOrigV_origV, trySyntheticN_disjunctN]

private theorem tryInvVar_disjEdge (a : N) (b : V) (ψ₁ ψ₂ : Formula N V X Y) (ws : Finset V') :
    tryInvVar (N := N) (V := V) (X := X) (Y := Y) ((hvn.origN a, hvv.origV b), hvn.disjunctN ψ₁ ψ₂, ws) = none := by
  simp only [tryInvVar, hvn.tryOrigN_origN, hvv.tryOrigV_origV, tryVarN_disjunctN]

private theorem tryInvPos_varEdge (a : N) (b : V) (x : X) (ws : Finset V') :
    tryInvPos (N := N) (V := V) (X := X) (Y := Y) ((hvn.origN a, hvv.origV b), hvn.varN (V := V) x, ws) = none := by
  simp only [tryInvPos, hvn.tryOrigN_origN, hvv.tryOrigV_origV, tryOrigN_varN]

private theorem tryInvNeg_varEdge (a : N) (b : V) (x : X) (ws : Finset V') :
    tryInvNeg (N := N) (V := V) (X := X) (Y := Y) ((hvn.origN a, hvv.origV b), hvn.varN (V := V) x, ws) = none := by
  simp only [tryInvNeg, hvn.tryOrigN_origN, hvv.tryOrigV_origV, trySyntheticN_varN]

private theorem tryInvDisj_varEdge (a : N) (b : V) (x : X) (ws : Finset V') :
    tryInvDisj (N := N) (V := V) (X := X) (Y := Y) ((hvn.origN a, hvv.origV b), hvn.varN (V := V) x, ws) = none := by
  simp only [tryInvDisj, hvn.tryOrigN_origN, hvv.tryOrigV_origV, tryDisjunctN_varN]

private theorem tryInvPos_nested (ψ₁ ψ₂ : Formula N V X Y) (b : V') (r : N' × Finset V') :
    tryInvPos (N := N) (V := V) (X := X) (Y := Y) ((hvn.disjunctN ψ₁ ψ₂, b), r) = none := by
  simp only [tryInvPos, tryOrigN_disjunctN]

private theorem tryInvNeg_nested (ψ₁ ψ₂ : Formula N V X Y) (b : V') (r : N' × Finset V') :
    tryInvNeg (N := N) (V := V) (X := X) (Y := Y) ((hvn.disjunctN ψ₁ ψ₂, b), r) = none := by
  simp only [tryInvNeg, tryOrigN_disjunctN]

private theorem tryInvDisj_nested (ψ₁ ψ₂ : Formula N V X Y) (b : V') (r : N' × Finset V') :
    tryInvDisj (N := N) (V := V) (X := X) (Y := Y) ((hvn.disjunctN ψ₁ ψ₂, b), r) = none := by
  simp only [tryInvDisj, tryOrigN_disjunctN]

private theorem tryInvVar_nested (ψ₁ ψ₂ : Formula N V X Y) (b : V') (r : N' × Finset V') :
    tryInvVar (N := N) (V := V) (X := X) (Y := Y) ((hvn.disjunctN ψ₁ ψ₂, b), r) = none := by
  simp only [tryInvVar, tryOrigN_disjunctN]

/-! ### Structure of the encoding's edge set -/

/-- Every atom of `ψ` contributes its edge to the encoding. -/
private theorem atomEdge_mem [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (Y_x : X → Finset Y) (k : ℕ) :
    ∀ ψ : Formula N V X Y, ψ.weight ≤ k → ∀ (q : Package N' V') (a : Atom N V X Y),
      a ∈ atoms Y_x ψ → atomEdge q a ∈ encodeNNF Y_x q ψ := by
  induction k with
  | zero =>
    intro ψ hw q a ha
    cases ψ with
    | dep n vs =>
      simp only [atoms, Finset.mem_singleton] at ha
      subst ha
      simp only [encodeNNF, atomEdge, Finset.mem_singleton]
    | varCmp x ω y =>
      simp only [atoms, Finset.mem_singleton] at ha
      subst ha
      simp [encodeNNF, atomEdge, cmpVersionSet]
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
    | varCmp x ω y =>
      simp only [atoms, Finset.mem_singleton] at ha
      subst ha
      simp [encodeNNF, atomEdge, cmpVersionSet]
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
      | varCmp x ω y =>
        simp only [atoms, Finset.mem_singleton] at ha
        subst ha
        simp [encodeNNF, atomEdge, cmpVersionSet]
      | conj ψL ψR =>
        simp only [Formula.weight] at hw
        have ha' : a ∈ atoms Y_x (Formula.disj (.neg ψL) (.neg ψR)) := by
          simpa only [atoms] using ha
        have h := ih (Formula.disj (.neg ψL) (.neg ψR))
          (by simp only [Formula.weight]; omega) q a ha'
        simpa only [encodeNNF] using h
      | disj ψL ψR =>
        simp only [Formula.weight] at hw
        have ha' : a ∈ atoms Y_x (Formula.conj (.neg ψL) (.neg ψR)) := by
          simpa only [atoms] using ha
        have h := ih (Formula.conj (.neg ψL) (.neg ψR))
          (by simp only [Formula.weight]; omega) q a ha'
        simpa only [encodeNNF] using h
      | neg ψ₁ =>
        simp only [Formula.weight] at hw
        have ha' : a ∈ atoms Y_x ψ₁ := by simpa only [atoms] using ha
        have h := ih ψ₁ (by omega) q a ha'
        simpa only [encodeNNF] using h

/-- Every edge of the encoding is a top-level atom edge, a nested edge (its
depender bears a disjunct-witness name), or a negative-literal guard edge. -/
private theorem encodeNNF_cases [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (Y_x : X → Finset Y) (k : ℕ) :
    ∀ ψ : Formula N V X Y, ψ.weight ≤ k → ∀ (q : Package N' V') e,
      e ∈ encodeNNF Y_x q ψ →
      (∃ a ∈ atoms Y_x ψ, e = atomEdge q a) ∨
      (∃ (φ₁ φ₂ : Formula N V X Y) (b : V'), e.1 = (hvn.disjunctN φ₁ φ₂, b)) ∨
      (∃ n vs u, u ∈ vs ∧
        e = ((hvn.origN n, hvv.origV u), hvn.syntheticN n vs, ({hvv.zeroV} : Finset V'))) := by
  induction k with
  | zero =>
    intro ψ hw q e he
    cases ψ with
    | dep n vs =>
      simp only [encodeNNF, Finset.mem_singleton] at he
      exact Or.inl ⟨.pos n vs, by simp [atoms], by rw [he]; rfl⟩
    | varCmp x ω y =>
      simp only [encodeNNF, Finset.mem_singleton] at he
      exact Or.inl ⟨.var x ((Y_x x).filter (fun y' => ω.eval y' y)), by simp [atoms],
        by rw [he]; simp [atomEdge, cmpVersionSet]⟩
    | conj ψL ψR => simp only [Formula.weight] at hw; omega
    | disj ψL ψR => simp only [Formula.weight] at hw; omega
    | neg ψ₀ => simp only [Formula.weight] at hw; omega
  | succ k ih =>
    intro ψ hw q e he
    cases ψ with
    | dep n vs =>
      simp only [encodeNNF, Finset.mem_singleton] at he
      exact Or.inl ⟨.pos n vs, by simp [atoms], by rw [he]; rfl⟩
    | varCmp x ω y =>
      simp only [encodeNNF, Finset.mem_singleton] at he
      exact Or.inl ⟨.var x ((Y_x x).filter (fun y' => ω.eval y' y)), by simp [atoms],
        by rw [he]; simp [atomEdge, cmpVersionSet]⟩
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
        · exact Or.inr (Or.inl ⟨ψL, ψR, hvv.zeroV, atomEdge_fst _ a⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases ih ψR (by omega) _ e he with ⟨a, _, rfl⟩ | h | h
        · exact Or.inr (Or.inl ⟨ψL, ψR, hvv.oneV, atomEdge_fst _ a⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    | neg ψ₀ =>
      cases ψ₀ with
      | dep n vs =>
        simp only [encodeNNF, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_image] at he
        rcases he with he | ⟨u, hu, heq⟩
        · exact Or.inl ⟨.neg n vs, by simp [atoms], by rw [he]; rfl⟩
        · exact Or.inr (Or.inr ⟨n, vs, u, hu, heq.symm⟩)
      | varCmp x ω y =>
        simp only [encodeNNF, Finset.mem_singleton] at he
        exact Or.inl ⟨.var x ((Y_x x).filter
            (fun y' => (CmpOp.complement ω).eval y' y)), by simp [atoms],
          by rw [he]; simp [atomEdge, cmpVersionSet]⟩
      | conj ψL ψR =>
        simp only [Formula.weight] at hw
        have he' : e ∈ encodeNNF Y_x q (Formula.disj (.neg ψL) (.neg ψR)) := by
          simpa only [encodeNNF] using he
        rcases ih (Formula.disj (.neg ψL) (.neg ψR))
            (by simp only [Formula.weight]; omega) q e he' with ⟨a, ha, rfl⟩ | h | h
        · exact Or.inl ⟨a, by simpa only [atoms] using ha, rfl⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      | disj ψL ψR =>
        simp only [Formula.weight] at hw
        have he' : e ∈ encodeNNF Y_x q (Formula.conj (.neg ψL) (.neg ψR)) := by
          simpa only [encodeNNF] using he
        rcases ih (Formula.conj (.neg ψL) (.neg ψR))
            (by simp only [Formula.weight]; omega) q e he' with ⟨a, ha, rfl⟩ | h | h
        · exact Or.inl ⟨a, by simpa only [atoms] using ha, rfl⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      | neg ψ₁ =>
        simp only [Formula.weight] at hw
        have he' : e ∈ encodeNNF Y_x q ψ₁ := by simpa only [encodeNNF] using he
        rcases ih ψ₁ (by omega) q e he' with ⟨a, ha, rfl⟩ | h | h
        · exact Or.inl ⟨a, by simpa only [atoms] using ha, rfl⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

/-! ### The atom-set retraction -/

/-- **Atom-set retraction for variable formulae.** The reduction erases
conjunction structure and entry boundaries, and normalises variable
comparisons to their extension over the declared domain; what it preserves —
exactly — is each depender's set of NNF atoms. No side-conditions are
required. -/
theorem liftAtoms_vfDeps [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (Y_x : X → Finset Y) (Δ_Ψ : VFDepRel N V X Y) :
    liftAtoms (vfDeps (N' := N') (V' := V') Y_x Δ_Ψ) =
      Δ_Ψ.biUnion (fun pψ => (atoms Y_x pψ.2).image (fun a => (pψ.1, a))) := by
  ext d
  simp only [liftAtoms, Finset.mem_biUnion, Finset.mem_union, Option.mem_toFinset,
    Option.mem_def, Finset.mem_image]
  constructor
  · rintro ⟨e, he, hdec⟩
    simp only [vfDeps, encode, Finset.mem_biUnion, Prod.exists] at he
    obtain ⟨p₁, p₂, ψ, hmem, hin⟩ := he
    rcases encodeNNF_cases Y_x ψ.weight ψ le_rfl _ e hin with ⟨a, ha, rfl⟩ |
      ⟨φ₁, φ₂, b, hfst⟩ | ⟨n, vs, u, hu, rfl⟩
    · cases a with
      | pos n vs =>
        simp only [atomEdge, embedPkg] at hdec
        rw [tryInvPos_eval, tryInvNeg_posEdge, tryInvDisj_posEdge, tryInvVar_posEdge] at hdec
        rcases hdec with ((hd | hd) | hd) | hd
        · obtain rfl := Option.some.inj hd
          exact ⟨((p₁, p₂), ψ), hmem, .pos n vs, ha, rfl⟩
        all_goals exact absurd hd (by simp)
      | neg n vs =>
        simp only [atomEdge, embedPkg] at hdec
        rw [tryInvPos_negEdge, tryInvNeg_eval, tryInvDisj_negEdge, tryInvVar_negEdge] at hdec
        rcases hdec with ((hd | hd) | hd) | hd
        · exact absurd hd (by simp)
        · obtain rfl := Option.some.inj hd
          exact ⟨((p₁, p₂), ψ), hmem, .neg n vs, ha, rfl⟩
        all_goals exact absurd hd (by simp)
      | disj ψ₁ ψ₂ =>
        simp only [atomEdge, embedPkg] at hdec
        rw [tryInvPos_disjEdge, tryInvNeg_disjEdge, tryInvDisj_eval, tryInvVar_disjEdge] at hdec
        rcases hdec with ((hd | hd) | hd) | hd
        · exact absurd hd (by simp)
        · exact absurd hd (by simp)
        · obtain rfl := Option.some.inj hd
          exact ⟨((p₁, p₂), ψ), hmem, .disj ψ₁ ψ₂, ha, rfl⟩
        · exact absurd hd (by simp)
      | var x ys =>
        simp only [atomEdge, embedPkg] at hdec
        rw [tryInvPos_varEdge, tryInvNeg_varEdge, tryInvDisj_varEdge, tryInvVar_eval] at hdec
        rcases hdec with ((hd | hd) | hd) | hd
        · exact absurd hd (by simp)
        · exact absurd hd (by simp)
        · exact absurd hd (by simp)
        · obtain rfl := Option.some.inj hd
          exact ⟨((p₁, p₂), ψ), hmem, .var x ys, ha, rfl⟩
    · obtain ⟨e1, e2⟩ := e
      subst hfst
      rw [tryInvPos_nested, tryInvNeg_nested, tryInvDisj_nested, tryInvVar_nested] at hdec
      rcases hdec with ((hd | hd) | hd) | hd <;> exact absurd hd (by simp)
    · rw [tryInvPos_negEdge, tryInvNeg_guard, tryInvDisj_negEdge, tryInvVar_negEdge] at hdec
      rcases hdec with ((hd | hd) | hd) | hd <;> exact absurd hd (by simp)
  · rintro ⟨⟨⟨p₁, p₂⟩, ψ⟩, hmem, a, ha, rfl⟩
    refine ⟨atomEdge (embedPkg (X := X) (Y := Y) (p₁, p₂)) a, ?_, ?_⟩
    · simp only [vfDeps, encode, Finset.mem_biUnion, Prod.exists]
      exact ⟨p₁, p₂, ψ, hmem, atomEdge_mem Y_x ψ.weight ψ le_rfl _ a ha⟩
    · cases a with
      | pos n vs =>
        simp only [atomEdge, embedPkg]
        rw [tryInvPos_eval]
        exact Or.inl (Or.inl (Or.inl rfl))
      | neg n vs =>
        simp only [atomEdge, embedPkg]
        rw [tryInvNeg_eval]
        exact Or.inl (Or.inl (Or.inr rfl))
      | disj ψ₁ ψ₂ =>
        simp only [atomEdge, embedPkg]
        rw [tryInvDisj_eval]
        exact Or.inl (Or.inr rfl)
      | var x ys =>
        simp only [atomEdge, embedPkg]
        rw [tryInvVar_eval]
        exact Or.inr rfl

/-! ### The atom set is a faithful normal form -/

private theorem satisfies_iff_atoms_aux [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (Y_x : X → Finset Y) (σ : X → Y) (hσ : ∀ x, σ x ∈ Y_x x) (k : ℕ) :
    ∀ ψ : Formula N V X Y, ψ.weight ≤ k → ∀ S : Finset (Package N V),
      ψ.satisfies S σ ↔ ∀ a ∈ atoms Y_x ψ, a.satisfies S σ := by
  induction k with
  | zero =>
    intro ψ hw S
    cases ψ with
    | dep n vs => simp [atoms, Atom.satisfies, Formula.satisfies]
    | varCmp x ω y =>
      simp [atoms, Atom.satisfies, Formula.satisfies, Finset.mem_filter, hσ x]
    | conj ψL ψR => simp only [Formula.weight] at hw; omega
    | disj ψL ψR => simp only [Formula.weight] at hw; omega
    | neg ψ₀ => simp only [Formula.weight] at hw; omega
  | succ k ih =>
    intro ψ hw S
    cases ψ with
    | dep n vs => simp [atoms, Atom.satisfies, Formula.satisfies]
    | varCmp x ω y =>
      simp [atoms, Atom.satisfies, Formula.satisfies, Finset.mem_filter, hσ x]
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
    | disj ψL ψR => simp [atoms, Atom.satisfies, Formula.satisfies]
    | neg ψ₀ =>
      cases ψ₀ with
      | dep n vs => simp [atoms, Atom.satisfies, Formula.satisfies]
      | varCmp x ω y =>
        simp [atoms, Atom.satisfies, Formula.satisfies, Finset.mem_filter, hσ x,
          complement_eval]
      | conj ψL ψR =>
        simp only [atoms, Atom.satisfies, Finset.mem_singleton, forall_eq]
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
          exact ⟨hL.mpr (fun a ha => h a (Or.inl ha)),
                 hR.mpr (fun a ha => h a (Or.inr ha))⟩
      | neg ψ₁ =>
        simp only [Formula.weight] at hw
        have h := ih ψ₁ (by omega) S
        simp only [atoms, Formula.satisfies, not_not]
        exact h

/-- The atom set is a faithful normal form: for an assignment within the
declared variable domains, a resolution and assignment satisfy a formula iff
they satisfy every one of its NNF atoms. -/
theorem satisfies_iff_atoms [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (Y_x : X → Finset Y) (S : Finset (Package N V)) (σ : X → Y)
    (hσ : ∀ x, σ x ∈ Y_x x) (ψ : Formula N V X Y) :
    ψ.satisfies S σ ↔ ∀ a ∈ atoms Y_x ψ, a.satisfies S σ :=
  satisfies_iff_atoms_aux Y_x σ hσ ψ.weight ψ le_rfl S

end PackageCalculus.VarFormula
