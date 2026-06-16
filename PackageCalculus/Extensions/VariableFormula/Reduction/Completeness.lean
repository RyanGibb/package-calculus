import PackageCalculus.Extensions.VariableFormula.Reduction.Definition
import Mathlib

namespace PackageCalculus.VarFormula

open Classical

variable {N : Type*} {V : Type*} {X : Type*} {Y : Type*}
variable {N' : Type*} {V' : Type*}
variable [DecidableEq N'] [DecidableEq V']
variable [hvn : HasVFNames N V X Y N'] [hvv : HasVFVersions V Y V']

/-! ## Dual-context witness construction (paper's `W^⊤ / W^⊥`).

Mirrors PF directly. There is no per-depender threading -- disjunction names
are per-formula, and the variable-comparison case contributes no witnesses
(`W^c(x ω y) = ∅`). -/

def witnessSetUntaken [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V)) :
    Formula N V X Y → Finset (Package N' V')
  | .dep _ _ => ∅
  | .conj ψ_L ψ_R =>
    witnessSetUntaken S_Ψ ψ_L ∪ witnessSetUntaken S_Ψ ψ_R
  | .disj ψ_L ψ_R =>
    witnessSetUntaken S_Ψ ψ_L ∪ witnessSetUntaken S_Ψ ψ_R
  | .varCmp _ _ _ => ∅
  | .neg (.dep n vs) =>
    if ∃ u ∈ vs, ((n, u) : Package N V) ∈ S_Ψ
    then {(hvn.syntheticN n vs, hvv.zeroV)}
    else ∅
  | .neg (.varCmp x ω y) =>
    witnessSetUntaken S_Ψ (.varCmp x (CmpOp.complement ω) y)
  | .neg (.conj ψ_L ψ_R) =>
    witnessSetUntaken S_Ψ (.disj (.neg ψ_L) (.neg ψ_R))
  | .neg (.disj ψ_L ψ_R) =>
    witnessSetUntaken S_Ψ (.conj (.neg ψ_L) (.neg ψ_R))
  | .neg (.neg ψ) =>
    witnessSetUntaken S_Ψ ψ
termination_by ψ => ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

def witnessSetTaken [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V)) (σ : X → Y) :
    Formula N V X Y → Finset (Package N' V')
  | .dep _ _ => ∅
  | .conj ψ_L ψ_R => witnessSetTaken S_Ψ σ ψ_L ∪ witnessSetTaken S_Ψ σ ψ_R
  | .disj ψ_L ψ_R =>
    if ψ_L.satisfies S_Ψ σ then
      {(hvn.disjunctN ψ_L ψ_R, hvv.zeroV)} ∪
        witnessSetTaken S_Ψ σ ψ_L ∪ witnessSetUntaken S_Ψ ψ_R
    else
      {(hvn.disjunctN ψ_L ψ_R, hvv.oneV)} ∪
        witnessSetUntaken S_Ψ ψ_L ∪ witnessSetTaken S_Ψ σ ψ_R
  | .varCmp _ _ _ => ∅
  | .neg (.dep n vs) => {(hvn.syntheticN n vs, hvv.oneV)}
  | .neg (.varCmp x ω y) =>
    witnessSetTaken S_Ψ σ (.varCmp x (CmpOp.complement ω) y)
  | .neg (.conj ψ_L ψ_R) =>
    witnessSetTaken S_Ψ σ (.disj (.neg ψ_L) (.neg ψ_R))
  | .neg (.disj ψ_L ψ_R) =>
    witnessSetTaken S_Ψ σ (.conj (.neg ψ_L) (.neg ψ_R))
  | .neg (.neg ψ) =>
    witnessSetTaken S_Ψ σ ψ
termination_by ψ => ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

/-- Completeness witness `S`: the original packages, plus formula witnesses
gated by whether the depender is in `S_Ψ`, plus the variable-assignment
packages `{(⟨x⟩, σ(x)) | x ∈ X}`. -/
def completenessWitness [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    [Fintype X]
    (S_Ψ : Finset (Package N V)) (Δ_Ψ : VFDepRel N V X Y)
    (σ : X → Y) :
    Finset (Package N' V') :=
  S_Ψ.image (embedPkg (X := X) (Y := Y)) ∪
  Δ_Ψ.biUnion (fun ⟨p, ψ⟩ =>
    if p ∈ S_Ψ then witnessSetTaken (N' := N') (V' := V') S_Ψ σ ψ
               else witnessSetUntaken (N' := N') (V' := V') S_Ψ ψ) ∪
  Finset.univ.image (fun x : X => ((hvn.varN x, hvv.varValV (σ x)) : Package N' V'))

/-! ## Subset of witnessPackages -/

lemma witnessSetUntaken_subset_witnessPackages [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V)) (p : Package N' V') (ψ : Formula N V X Y) :
    witnessSetUntaken (N' := N') (V' := V') S_Ψ ψ ⊆ witnessPackages p ψ := by
  induction' n : ψ.weight using Nat.strong_induction_on with n ih generalizing ψ p S_Ψ;
  rcases ψ with ( _ | ⟨ ψ₁, ψ₂ ⟩ | ⟨ ψ₁, ψ₂ ⟩ | ⟨ x, ω, y ⟩ | ⟨ n, vs ⟩ );
  all_goals unfold witnessSetUntaken witnessPackages; simp +decide [ Finset.subset_iff ];
  any_goals intro a b hab; exact ih _ ( by simp +decide [ Formula.weight ] at n ⊢; linarith ) _ _ _ rfl hab;
  · rintro a b ( h | h ) <;> [ exact Or.inl ( ih _ ( by simp +decide [ Formula.weight ] at n ⊢; linarith ) _ _ _ rfl h ) ; exact Or.inr ( ih _ ( by simp +decide [ Formula.weight ] at n ⊢; linarith ) _ _ _ rfl h ) ];
  · rintro a b ( h | h ) <;> [ exact Or.inr ( Or.inr ( Or.inl ( ih _ ( by simp +decide [ Formula.weight ] at n ⊢; linarith ) _ _ _ rfl h ) ) ) ; exact Or.inr ( Or.inr ( Or.inr ( ih _ ( by simp +decide [ Formula.weight ] at n ⊢; linarith ) _ _ _ rfl h ) ) ) ];
  · split_ifs <;> simp_all +decide [ Finset.subset_iff ]

lemma witnessSetTaken_subset_witnessPackages [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V)) (σ : X → Y) (p : Package N' V') (ψ : Formula N V X Y) :
    witnessSetTaken (N' := N') (V' := V') S_Ψ σ ψ ⊆ witnessPackages p ψ := by
  intro q hq
  match ψ with
  | .dep _ _ => simp [witnessSetTaken] at hq
  | .conj ψ_L ψ_R =>
    unfold witnessSetTaken at hq; unfold witnessPackages
    simp only [Finset.mem_union] at hq ⊢
    exact hq.elim
      (fun h => Or.inl (witnessSetTaken_subset_witnessPackages S_Ψ σ p ψ_L h))
      (fun h => Or.inr (witnessSetTaken_subset_witnessPackages S_Ψ σ p ψ_R h))
  | .disj ψ_L ψ_R =>
    show q ∈ witnessPackages p (.disj ψ_L ψ_R)
    rw [witnessSetTaken.eq_3] at hq
    rw [witnessPackages.eq_3]
    split at hq <;> simp only [Finset.mem_union, Finset.mem_singleton] at hq <;>
        rcases hq with (rfl | h) | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (witnessSetTaken_subset_witnessPackages S_Ψ σ _ ψ_L h))
    · exact Finset.mem_union_right _ (witnessSetUntaken_subset_witnessPackages S_Ψ _ ψ_R h)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (witnessSetUntaken_subset_witnessPackages S_Ψ _ ψ_L h))
    · exact Finset.mem_union_right _ (witnessSetTaken_subset_witnessPackages S_Ψ σ _ ψ_R h)
  | .varCmp _ _ _ => simp [witnessSetTaken] at hq
  | .neg (.dep n vs) =>
    unfold witnessSetTaken at hq; unfold witnessPackages
    simp only [Finset.mem_singleton] at hq; subst hq
    simp [Finset.mem_insert]
  | .neg (.varCmp x ω y) =>
    rw [witnessSetTaken.eq_6] at hq
    rw [witnessPackages.eq_6]
    exact witnessSetTaken_subset_witnessPackages S_Ψ σ p _ hq
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetTaken.eq_7] at hq
    rw [witnessPackages.eq_7]
    exact witnessSetTaken_subset_witnessPackages S_Ψ σ p _ hq
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetTaken.eq_8] at hq
    rw [witnessPackages.eq_8]
    exact witnessSetTaken_subset_witnessPackages S_Ψ σ p _ hq
  | .neg (.neg ψ') =>
    rw [witnessSetTaken.eq_9] at hq
    rw [witnessPackages.eq_9]
    exact witnessSetTaken_subset_witnessPackages S_Ψ σ p _ hq
  termination_by ψ.weight
  decreasing_by all_goals simp only [Formula.weight]; omega

/-! ## Determinism lemmas on `witnessSetUntaken` -/

lemma witnessSetUntaken_negDep_det [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V X Y) (n : N) (vs : Finset V) (v : V')
    (h : (hvn.syntheticN n vs, v) ∈ witnessSetUntaken S_Ψ ψ) :
    v = hvv.zeroV := by
  match ψ with
  | .dep _ _ => exact absurd h (by rw [witnessSetUntaken.eq_1]; exact Finset.notMem_empty _)
  | .conj ψ_L ψ_R =>
    simp only [witnessSetUntaken.eq_2, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_negDep_det S_Ψ ψ_L n vs v)
      (witnessSetUntaken_negDep_det S_Ψ ψ_R n vs v)
  | .disj ψ_L ψ_R =>
    simp only [witnessSetUntaken.eq_3, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_negDep_det S_Ψ ψ_L n vs v)
      (witnessSetUntaken_negDep_det S_Ψ ψ_R n vs v)
  | .varCmp _ _ _ => exact absurd h (by rw [witnessSetUntaken.eq_4]; exact Finset.notMem_empty _)
  | .neg (.dep n' vs') =>
    rw [witnessSetUntaken.eq_5] at h
    split at h
    · simp only [Finset.mem_singleton, Prod.mk.injEq] at h
      exact h.2
    · simp at h
  | .neg (.varCmp x ω y) =>
    rw [witnessSetUntaken.eq_6] at h
    exact witnessSetUntaken_negDep_det S_Ψ _ n vs v h
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetUntaken.eq_7] at h
    exact witnessSetUntaken_negDep_det S_Ψ (.disj (.neg ψ_L) (.neg ψ_R)) n vs v h
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetUntaken.eq_8] at h
    exact witnessSetUntaken_negDep_det S_Ψ (.conj (.neg ψ_L) (.neg ψ_R)) n vs v h
  | .neg (.neg ψ') =>
    rw [witnessSetUntaken.eq_9] at h
    exact witnessSetUntaken_negDep_det S_Ψ ψ' n vs v h
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

lemma witnessSetUntaken_negDep_exists [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V X Y) (n : N) (vs : Finset V) (v : V')
    (h : (hvn.syntheticN n vs, v) ∈ witnessSetUntaken S_Ψ ψ) :
    ∃ u ∈ vs, ((n, u) : Package N V) ∈ S_Ψ := by
  match ψ with
  | .dep _ _ => exact absurd h (by rw [witnessSetUntaken.eq_1]; exact Finset.notMem_empty _)
  | .conj ψ_L ψ_R =>
    simp only [witnessSetUntaken.eq_2, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_negDep_exists S_Ψ ψ_L n vs v)
      (witnessSetUntaken_negDep_exists S_Ψ ψ_R n vs v)
  | .disj ψ_L ψ_R =>
    simp only [witnessSetUntaken.eq_3, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_negDep_exists S_Ψ ψ_L n vs v)
      (witnessSetUntaken_negDep_exists S_Ψ ψ_R n vs v)
  | .varCmp _ _ _ => exact absurd h (by rw [witnessSetUntaken.eq_4]; exact Finset.notMem_empty _)
  | .neg (.dep n' vs') =>
    rw [witnessSetUntaken.eq_5] at h
    split at h
    · rename_i hex
      simp only [Finset.mem_singleton] at h
      have heq := (Prod.mk.injEq _ _ _ _).mp h
      obtain ⟨rfl, rfl⟩ := hvn.syntheticN_injective heq.1
      exact hex
    · simp at h
  | .neg (.varCmp x ω y) =>
    rw [witnessSetUntaken.eq_6] at h
    exact witnessSetUntaken_negDep_exists S_Ψ _ n vs v h
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetUntaken.eq_7] at h
    exact witnessSetUntaken_negDep_exists S_Ψ (.disj (.neg ψ_L) (.neg ψ_R)) n vs v h
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetUntaken.eq_8] at h
    exact witnessSetUntaken_negDep_exists S_Ψ (.conj (.neg ψ_L) (.neg ψ_R)) n vs v h
  | .neg (.neg ψ') =>
    rw [witnessSetUntaken.eq_9] at h
    exact witnessSetUntaken_negDep_exists S_Ψ ψ' n vs v h
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

lemma witnessSetUntaken_disjunct_det [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V X Y) (ψ_L ψ_R : Formula N V X Y) (v : V')
    (h : (hvn.disjunctN ψ_L ψ_R, v) ∈ witnessSetUntaken (N' := N') S_Ψ ψ) : False := by
  match ψ with
  | .dep _ _ => exact absurd h (by rw [witnessSetUntaken.eq_1]; exact Finset.notMem_empty _)
  | .conj ψ_a ψ_b =>
    simp only [witnessSetUntaken.eq_2, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_disjunct_det S_Ψ ψ_a ψ_L ψ_R v)
      (witnessSetUntaken_disjunct_det S_Ψ ψ_b ψ_L ψ_R v)
  | .disj ψ_a ψ_b =>
    simp only [witnessSetUntaken.eq_3, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_disjunct_det S_Ψ ψ_a ψ_L ψ_R v)
      (witnessSetUntaken_disjunct_det S_Ψ ψ_b ψ_L ψ_R v)
  | .varCmp _ _ _ => exact absurd h (by rw [witnessSetUntaken.eq_4]; exact Finset.notMem_empty _)
  | .neg (.dep _ _) =>
    rw [witnessSetUntaken.eq_5] at h
    split at h
    · simp only [Finset.mem_singleton, Prod.mk.injEq] at h
      exact absurd h.1 (hvn.disjunctN_ne_syntheticN _ _ _ _)
    · simp at h
  | .neg (.varCmp x ω y) =>
    rw [witnessSetUntaken.eq_6] at h
    exact witnessSetUntaken_disjunct_det S_Ψ _ ψ_L ψ_R v h
  | .neg (.conj ψ_a ψ_b) =>
    rw [witnessSetUntaken.eq_7] at h
    exact witnessSetUntaken_disjunct_det S_Ψ (.disj (.neg ψ_a) (.neg ψ_b)) ψ_L ψ_R v h
  | .neg (.disj ψ_a ψ_b) =>
    rw [witnessSetUntaken.eq_8] at h
    exact witnessSetUntaken_disjunct_det S_Ψ (.conj (.neg ψ_a) (.neg ψ_b)) ψ_L ψ_R v h
  | .neg (.neg ψ') =>
    rw [witnessSetUntaken.eq_9] at h
    exact witnessSetUntaken_disjunct_det S_Ψ ψ' ψ_L ψ_R v h
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

/-! ## Taken-side disjunctN determinism -/

lemma witnessSetTaken_disjunct_det [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V)) (σ : X → Y)
    (ψ : Formula N V X Y) (ψ_L ψ_R : Formula N V X Y) (v : V')
    (h : (hvn.disjunctN ψ_L ψ_R, v) ∈ witnessSetTaken (N' := N') S_Ψ σ ψ) :
    v = if ψ_L.satisfies S_Ψ σ then hvv.zeroV else hvv.oneV := by
  match ψ with
  | .dep _ _ => exact absurd h (by rw [witnessSetTaken.eq_1]; exact Finset.notMem_empty _)
  | .conj ψ_a ψ_b =>
    simp only [witnessSetTaken.eq_2, Finset.mem_union] at h
    exact h.elim
      (witnessSetTaken_disjunct_det S_Ψ σ ψ_a ψ_L ψ_R v)
      (witnessSetTaken_disjunct_det S_Ψ σ ψ_b ψ_L ψ_R v)
  | .disj ψ_a ψ_b =>
    simp only [witnessSetTaken.eq_3] at h
    split at h
    · rename_i hψa_sat
      simp only [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with (hsing | hL) | hU
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        obtain ⟨rfl, rfl⟩ := hvn.disjunctN_injective heq.1
        simp [hψa_sat, heq.2]
      · exact witnessSetTaken_disjunct_det S_Ψ σ ψ_a ψ_L ψ_R v hL
      · exact (witnessSetUntaken_disjunct_det S_Ψ ψ_b ψ_L ψ_R v hU).elim
    · rename_i hψa_unsat
      simp only [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with (hsing | hU) | hR
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        obtain ⟨rfl, rfl⟩ := hvn.disjunctN_injective heq.1
        simp [hψa_unsat, heq.2]
      · exact (witnessSetUntaken_disjunct_det S_Ψ ψ_a ψ_L ψ_R v hU).elim
      · exact witnessSetTaken_disjunct_det S_Ψ σ ψ_b ψ_L ψ_R v hR
  | .varCmp _ _ _ => exact absurd h (by rw [witnessSetTaken.eq_4]; exact Finset.notMem_empty _)
  | .neg (.dep _ _) =>
    simp only [witnessSetTaken.eq_5, Finset.mem_singleton, Prod.mk.injEq] at h
    exact absurd h.1 (hvn.disjunctN_ne_syntheticN _ _ _ _)
  | .neg (.varCmp x ω y) =>
    rw [witnessSetTaken.eq_6] at h
    exact witnessSetTaken_disjunct_det S_Ψ σ _ ψ_L ψ_R v h
  | .neg (.conj ψ_a ψ_b) =>
    rw [witnessSetTaken.eq_7] at h
    exact witnessSetTaken_disjunct_det S_Ψ σ (.disj (.neg ψ_a) (.neg ψ_b)) ψ_L ψ_R v h
  | .neg (.disj ψ_a ψ_b) =>
    rw [witnessSetTaken.eq_8] at h
    exact witnessSetTaken_disjunct_det S_Ψ σ (.conj (.neg ψ_a) (.neg ψ_b)) ψ_L ψ_R v h
  | .neg (.neg ψ') =>
    rw [witnessSetTaken.eq_9] at h
    exact witnessSetTaken_disjunct_det S_Ψ σ ψ' ψ_L ψ_R v h
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

/-! ## Taken-side syntheticN determinism (satisfaction-aware) -/

lemma witnessSetTaken_negDep_det [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V)) (σ : X → Y)
    (ψ : Formula N V X Y) (hsat : ψ.satisfies S_Ψ σ)
    (n : N) (vs : Finset V) (v : V')
    (h : (hvn.syntheticN n vs, v) ∈ witnessSetTaken (N' := N') S_Ψ σ ψ) :
    v = if ∃ u ∈ vs, ((n, u) : Package N V) ∈ S_Ψ then hvv.zeroV else hvv.oneV := by
  match ψ with
  | .dep _ _ => exact absurd h (by rw [witnessSetTaken.eq_1]; exact Finset.notMem_empty _)
  | .conj ψ_L ψ_R =>
    simp only [witnessSetTaken.eq_2, Finset.mem_union] at h
    rcases h with hL | hR
    · exact witnessSetTaken_negDep_det S_Ψ σ ψ_L hsat.1 n vs v hL
    · exact witnessSetTaken_negDep_det S_Ψ σ ψ_R hsat.2 n vs v hR
  | .disj ψ_L ψ_R =>
    simp only [witnessSetTaken.eq_3] at h
    split at h
    · rename_i hψL_sat
      simp only [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with (hsing | hL) | hU
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        exact absurd heq.1 (hvn.syntheticN_ne_disjunctN _ _ _ _)
      · exact witnessSetTaken_negDep_det S_Ψ σ ψ_L hψL_sat n vs v hL
      · have hv := witnessSetUntaken_negDep_det S_Ψ ψ_R n vs v hU
        have hex := witnessSetUntaken_negDep_exists S_Ψ ψ_R n vs v hU
        simp [hv, hex]
    · rename_i hψL_unsat
      simp only [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with (hsing | hU) | hR
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        exact absurd heq.1 (hvn.syntheticN_ne_disjunctN _ _ _ _)
      · have hv := witnessSetUntaken_negDep_det S_Ψ ψ_L n vs v hU
        have hex := witnessSetUntaken_negDep_exists S_Ψ ψ_L n vs v hU
        simp [hv, hex]
      · exact witnessSetTaken_negDep_det S_Ψ σ ψ_R (hsat.resolve_left hψL_unsat) n vs v hR
  | .varCmp _ _ _ => exact absurd h (by rw [witnessSetTaken.eq_4]; exact Finset.notMem_empty _)
  | .neg (.dep n' vs') =>
    simp only [witnessSetTaken.eq_5, Finset.mem_singleton] at h
    have heq := (Prod.mk.injEq _ _ _ _).mp h
    obtain ⟨rfl, rfl⟩ := hvn.syntheticN_injective heq.1
    rw [heq.2]
    have : ¬ ∃ u ∈ vs, ((n, u) : Package N V) ∈ S_Ψ := hsat
    simp [this]
  | .neg (.varCmp x ω y) =>
    rw [witnessSetTaken.eq_6] at h
    apply witnessSetTaken_negDep_det S_Ψ σ _ _ n vs v h
    -- hsat : ¬(.varCmp x ω y).satisfies = ¬ω.eval (σ x) y
    -- need: (.varCmp x (complement ω) y).satisfies = (complement ω).eval (σ x) y
    show (CmpOp.complement ω).eval (σ x) y = true
    exact (complement_eval ω _ _).mpr hsat
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetTaken.eq_7] at h
    apply witnessSetTaken_negDep_det S_Ψ σ (.disj (.neg ψ_L) (.neg ψ_R)) _ n vs v h
    simp only [Formula.satisfies] at hsat
    exact (not_and_or.mp hsat)
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetTaken.eq_8] at h
    apply witnessSetTaken_negDep_det S_Ψ σ (.conj (.neg ψ_L) (.neg ψ_R)) _ n vs v h
    simp only [Formula.satisfies] at hsat
    exact (not_or.mp hsat)
  | .neg (.neg ψ') =>
    rw [witnessSetTaken.eq_9] at h
    apply witnessSetTaken_negDep_det S_Ψ σ ψ' _ n vs v h
    simp only [Formula.satisfies] at hsat
    exact not_not.mp hsat
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

/-! ## Name classification: witnessSet only contains syntheticN / disjunctN -/

lemma witnessSetUntaken_name_classify [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V X Y) (n : N') (v : V')
    (h : (n, v) ∈ witnessSetUntaken S_Ψ ψ) :
    (∃ n' vs, n = hvn.syntheticN n' vs) ∨ (∃ ψ_L ψ_R, n = hvn.disjunctN ψ_L ψ_R) := by
  match ψ with
  | .dep _ _ => exact absurd h (by rw [witnessSetUntaken.eq_1]; exact Finset.notMem_empty _)
  | .conj ψ_L ψ_R =>
    simp only [witnessSetUntaken.eq_2, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_name_classify S_Ψ ψ_L n v)
      (witnessSetUntaken_name_classify S_Ψ ψ_R n v)
  | .disj ψ_L ψ_R =>
    simp only [witnessSetUntaken.eq_3, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_name_classify S_Ψ ψ_L n v)
      (witnessSetUntaken_name_classify S_Ψ ψ_R n v)
  | .varCmp _ _ _ => exact absurd h (by rw [witnessSetUntaken.eq_4]; exact Finset.notMem_empty _)
  | .neg (.dep n' vs) =>
    rw [witnessSetUntaken.eq_5] at h
    split at h
    · simp only [Finset.mem_singleton] at h
      have heq := (Prod.mk.injEq _ _ _ _).mp h
      exact Or.inl ⟨n', vs, heq.1⟩
    · simp at h
  | .neg (.varCmp x ω y) =>
    rw [witnessSetUntaken.eq_6] at h
    exact witnessSetUntaken_name_classify S_Ψ _ n v h
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetUntaken.eq_7] at h
    exact witnessSetUntaken_name_classify S_Ψ (.disj (.neg ψ_L) (.neg ψ_R)) n v h
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetUntaken.eq_8] at h
    exact witnessSetUntaken_name_classify S_Ψ (.conj (.neg ψ_L) (.neg ψ_R)) n v h
  | .neg (.neg ψ') =>
    rw [witnessSetUntaken.eq_9] at h
    exact witnessSetUntaken_name_classify S_Ψ ψ' n v h
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

lemma witnessSetTaken_name_classify [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V)) (σ : X → Y)
    (ψ : Formula N V X Y) (n : N') (v : V')
    (h : (n, v) ∈ witnessSetTaken S_Ψ σ ψ) :
    (∃ n' vs, n = hvn.syntheticN n' vs) ∨ (∃ ψ_L ψ_R, n = hvn.disjunctN ψ_L ψ_R) := by
  match ψ with
  | .dep _ _ => exact absurd h (by rw [witnessSetTaken.eq_1]; exact Finset.notMem_empty _)
  | .conj ψ_L ψ_R =>
    simp only [witnessSetTaken.eq_2, Finset.mem_union] at h
    exact h.elim
      (witnessSetTaken_name_classify S_Ψ σ ψ_L n v)
      (witnessSetTaken_name_classify S_Ψ σ ψ_R n v)
  | .disj ψ_L ψ_R =>
    simp only [witnessSetTaken.eq_3] at h
    split at h
    · simp only [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with (hsing | hL) | hU
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        exact Or.inr ⟨ψ_L, ψ_R, heq.1⟩
      · exact witnessSetTaken_name_classify S_Ψ σ ψ_L n v hL
      · exact witnessSetUntaken_name_classify S_Ψ ψ_R n v hU
    · simp only [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with (hsing | hU) | hR
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        exact Or.inr ⟨ψ_L, ψ_R, heq.1⟩
      · exact witnessSetUntaken_name_classify S_Ψ ψ_L n v hU
      · exact witnessSetTaken_name_classify S_Ψ σ ψ_R n v hR
  | .varCmp _ _ _ => exact absurd h (by rw [witnessSetTaken.eq_4]; exact Finset.notMem_empty _)
  | .neg (.dep n' vs) =>
    simp only [witnessSetTaken.eq_5, Finset.mem_singleton] at h
    have heq := (Prod.mk.injEq _ _ _ _).mp h
    exact Or.inl ⟨n', vs, heq.1⟩
  | .neg (.varCmp x ω y) =>
    rw [witnessSetTaken.eq_6] at h
    exact witnessSetTaken_name_classify S_Ψ σ _ n v h
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetTaken.eq_7] at h
    exact witnessSetTaken_name_classify S_Ψ σ (.disj (.neg ψ_L) (.neg ψ_R)) n v h
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetTaken.eq_8] at h
    exact witnessSetTaken_name_classify S_Ψ σ (.conj (.neg ψ_L) (.neg ψ_R)) n v h
  | .neg (.neg ψ') =>
    rw [witnessSetTaken.eq_9] at h
    exact witnessSetTaken_name_classify S_Ψ σ ψ' n v h
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

/-! ## No original-name or variable-name witnesses -/

lemma witnessSetUntaken_not_orig [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V)) (ψ : Formula N V X Y) (n : N) (v : V') :
    (hvn.origN n, v) ∉ witnessSetUntaken S_Ψ ψ := fun h => by
  rcases witnessSetUntaken_name_classify S_Ψ ψ _ v h with ⟨m, vs, he⟩ | ⟨ψ_L, ψ_R, he⟩
  · exact hvn.origN_ne_syntheticN n m vs he
  · exact hvn.origN_ne_disjunctN n ψ_L ψ_R he

lemma witnessSetTaken_not_orig [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V)) (σ : X → Y) (ψ : Formula N V X Y) (n : N) (v : V') :
    (hvn.origN n, v) ∉ witnessSetTaken S_Ψ σ ψ := fun h => by
  rcases witnessSetTaken_name_classify S_Ψ σ ψ _ v h with ⟨m, vs, he⟩ | ⟨ψ_L, ψ_R, he⟩
  · exact hvn.origN_ne_syntheticN n m vs he
  · exact hvn.origN_ne_disjunctN n ψ_L ψ_R he

lemma witnessSetUntaken_not_varN [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V)) (ψ : Formula N V X Y) (x : X) (v : V') :
    (hvn.varN x, v) ∉ witnessSetUntaken S_Ψ ψ := fun h => by
  rcases witnessSetUntaken_name_classify S_Ψ ψ _ v h with ⟨m, vs, he⟩ | ⟨ψ_L, ψ_R, he⟩
  · exact hvn.varN_ne_syntheticN x m vs he
  · exact hvn.varN_ne_disjunctN x ψ_L ψ_R he

lemma witnessSetTaken_not_varN [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V)) (σ : X → Y) (ψ : Formula N V X Y) (x : X) (v : V') :
    (hvn.varN x, v) ∉ witnessSetTaken S_Ψ σ ψ := fun h => by
  rcases witnessSetTaken_name_classify S_Ψ σ ψ _ v h with ⟨m, vs, he⟩ | ⟨ψ_L, ψ_R, he⟩
  · exact hvn.varN_ne_syntheticN x m vs he
  · exact hvn.varN_ne_disjunctN x ψ_L ψ_R he

/-! ## Disjunct monotonicity (taken side) -/

private lemma witnessSetTaken_disj_zero_mono [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V)) (σ : X → Y)
    (ψ : Formula N V X Y)
    (ψ_L ψ_R : Formula N V X Y)
    (hw : (hvn.disjunctN ψ_L ψ_R, hvv.zeroV) ∈ witnessSetTaken (N' := N') S_Ψ σ ψ) :
    (ψ_L.satisfies S_Ψ σ) ∧
      witnessSetTaken (N' := N') (V' := V') S_Ψ σ ψ_L ⊆ witnessSetTaken S_Ψ σ ψ ∧
      witnessSetUntaken (N' := N') (V' := V') S_Ψ ψ_R ⊆ witnessSetTaken S_Ψ σ ψ := by
  match ψ with
  | .dep _ _ => exact absurd hw (by rw [witnessSetTaken.eq_1]; exact Finset.notMem_empty _)
  | .conj ψ_a ψ_b =>
    simp only [witnessSetTaken.eq_2, Finset.mem_union] at hw
    rcases hw with hL | hR
    · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_zero_mono S_Ψ σ ψ_a ψ_L ψ_R hL
      exact ⟨hs, fun x hx => by simp only [witnessSetTaken.eq_2]; exact Finset.mem_union.mpr (Or.inl (h1 hx)),
             fun x hx => by simp only [witnessSetTaken.eq_2]; exact Finset.mem_union.mpr (Or.inl (h2 hx))⟩
    · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_zero_mono S_Ψ σ ψ_b ψ_L ψ_R hR
      exact ⟨hs, fun x hx => by simp only [witnessSetTaken.eq_2]; exact Finset.mem_union.mpr (Or.inr (h1 hx)),
             fun x hx => by simp only [witnessSetTaken.eq_2]; exact Finset.mem_union.mpr (Or.inr (h2 hx))⟩
  | .disj ψ_a ψ_b =>
    simp only [witnessSetTaken.eq_3] at hw
    split at hw
    · rename_i hψa_sat
      simp only [Finset.mem_union, Finset.mem_singleton] at hw
      rcases hw with (hsing | hL) | hU
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        obtain ⟨rfl, rfl⟩ := hvn.disjunctN_injective heq.1
        refine ⟨hψa_sat, ?_, ?_⟩
        · intro x hx; simp only [witnessSetTaken.eq_3, if_pos hψa_sat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inl (Or.inr hx)
        · intro x hx; simp only [witnessSetTaken.eq_3, if_pos hψa_sat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inr hx
      · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_zero_mono S_Ψ σ ψ_a ψ_L ψ_R hL
        refine ⟨hs, ?_, ?_⟩ <;> {
          intro x hx; simp only [witnessSetTaken.eq_3, if_pos hψa_sat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inl (Or.inr (by first | exact h1 hx | exact h2 hx)) }
      · exact absurd hU (witnessSetUntaken_disjunct_det S_Ψ ψ_b ψ_L ψ_R _)
    · rename_i hψa_unsat
      simp only [Finset.mem_union, Finset.mem_singleton] at hw
      rcases hw with (hsing | hU) | hR
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        exact absurd heq.2 hvv.zeroV_ne_oneV
      · exact absurd hU (witnessSetUntaken_disjunct_det S_Ψ ψ_a ψ_L ψ_R _)
      · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_zero_mono S_Ψ σ ψ_b ψ_L ψ_R hR
        refine ⟨hs, ?_, ?_⟩ <;> {
          intro x hx; simp only [witnessSetTaken.eq_3, if_neg hψa_unsat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inr (by first | exact h1 hx | exact h2 hx) }
  | .varCmp _ _ _ => exact absurd hw (by rw [witnessSetTaken.eq_4]; exact Finset.notMem_empty _)
  | .neg (.dep n vs) =>
    simp only [witnessSetTaken.eq_5, Finset.mem_singleton, Prod.mk.injEq] at hw
    exact absurd hw.1 (hvn.disjunctN_ne_syntheticN ψ_L ψ_R n vs)
  | .neg (.varCmp x ω y) =>
    rw [witnessSetTaken.eq_6] at hw ⊢
    exact witnessSetTaken_disj_zero_mono S_Ψ σ _ ψ_L ψ_R hw
  | .neg (.conj ψ_a ψ_b) =>
    rw [witnessSetTaken.eq_7] at hw ⊢
    exact witnessSetTaken_disj_zero_mono S_Ψ σ (.disj (.neg ψ_a) (.neg ψ_b)) ψ_L ψ_R hw
  | .neg (.disj ψ_a ψ_b) =>
    rw [witnessSetTaken.eq_8] at hw ⊢
    exact witnessSetTaken_disj_zero_mono S_Ψ σ (.conj (.neg ψ_a) (.neg ψ_b)) ψ_L ψ_R hw
  | .neg (.neg ψ') =>
    rw [witnessSetTaken.eq_9] at hw ⊢
    exact witnessSetTaken_disj_zero_mono S_Ψ σ ψ' ψ_L ψ_R hw
termination_by ψ.weight
decreasing_by all_goals (simp only [Formula.weight]; omega)

private lemma witnessSetTaken_disj_one_mono [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S_Ψ : Finset (Package N V)) (σ : X → Y)
    (ψ : Formula N V X Y) (hsat : ψ.satisfies S_Ψ σ)
    (ψ_L ψ_R : Formula N V X Y)
    (hw : (hvn.disjunctN ψ_L ψ_R, hvv.oneV) ∈ witnessSetTaken (N' := N') S_Ψ σ ψ) :
    (ψ_R.satisfies S_Ψ σ) ∧
      witnessSetUntaken (N' := N') (V' := V') S_Ψ ψ_L ⊆ witnessSetTaken S_Ψ σ ψ ∧
      witnessSetTaken (N' := N') (V' := V') S_Ψ σ ψ_R ⊆ witnessSetTaken S_Ψ σ ψ := by
  match ψ with
  | .dep _ _ => exact absurd hw (by rw [witnessSetTaken.eq_1]; exact Finset.notMem_empty _)
  | .conj ψ_a ψ_b =>
    simp only [witnessSetTaken.eq_2, Finset.mem_union] at hw
    rcases hw with hL | hR
    · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_one_mono S_Ψ σ ψ_a hsat.1 ψ_L ψ_R hL
      exact ⟨hs, fun x hx => by simp only [witnessSetTaken.eq_2]; exact Finset.mem_union.mpr (Or.inl (h1 hx)),
             fun x hx => by simp only [witnessSetTaken.eq_2]; exact Finset.mem_union.mpr (Or.inl (h2 hx))⟩
    · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_one_mono S_Ψ σ ψ_b hsat.2 ψ_L ψ_R hR
      exact ⟨hs, fun x hx => by simp only [witnessSetTaken.eq_2]; exact Finset.mem_union.mpr (Or.inr (h1 hx)),
             fun x hx => by simp only [witnessSetTaken.eq_2]; exact Finset.mem_union.mpr (Or.inr (h2 hx))⟩
  | .disj ψ_a ψ_b =>
    simp only [witnessSetTaken.eq_3] at hw
    split at hw
    · rename_i hψa_sat
      simp only [Finset.mem_union, Finset.mem_singleton] at hw
      rcases hw with (hsing | hL) | hU
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        exact absurd heq.2.symm hvv.zeroV_ne_oneV
      · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_one_mono S_Ψ σ ψ_a hψa_sat ψ_L ψ_R hL
        refine ⟨hs, ?_, ?_⟩ <;> {
          intro x hx; simp only [witnessSetTaken.eq_3, if_pos hψa_sat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inl (Or.inr (by first | exact h1 hx | exact h2 hx)) }
      · exact absurd hU (witnessSetUntaken_disjunct_det S_Ψ ψ_b ψ_L ψ_R _)
    · rename_i hψa_unsat
      simp only [Finset.mem_union, Finset.mem_singleton] at hw
      rcases hw with (hsing | hU) | hR
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        obtain ⟨rfl, rfl⟩ := hvn.disjunctN_injective heq.1
        refine ⟨hsat.resolve_left hψa_unsat, ?_, ?_⟩
        · intro x hx; simp only [witnessSetTaken.eq_3, if_neg hψa_unsat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inl (Or.inr hx)
        · intro x hx; simp only [witnessSetTaken.eq_3, if_neg hψa_unsat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inr hx
      · exact absurd hU (witnessSetUntaken_disjunct_det S_Ψ ψ_a ψ_L ψ_R _)
      · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_one_mono S_Ψ σ ψ_b (hsat.resolve_left hψa_unsat) ψ_L ψ_R hR
        refine ⟨hs, ?_, ?_⟩ <;> {
          intro x hx; simp only [witnessSetTaken.eq_3, if_neg hψa_unsat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inr (by first | exact h1 hx | exact h2 hx) }
  | .varCmp _ _ _ => exact absurd hw (by rw [witnessSetTaken.eq_4]; exact Finset.notMem_empty _)
  | .neg (.dep n vs) =>
    simp only [witnessSetTaken.eq_5, Finset.mem_singleton, Prod.mk.injEq] at hw
    exact absurd hw.1 (hvn.disjunctN_ne_syntheticN ψ_L ψ_R n vs)
  | .neg (.varCmp x ω y) =>
    rw [witnessSetTaken.eq_6] at hw ⊢
    apply witnessSetTaken_disj_one_mono S_Ψ σ _ _ ψ_L ψ_R hw
    show (CmpOp.complement ω).eval (σ x) y = true
    exact (complement_eval ω _ _).mpr hsat
  | .neg (.conj ψ_a ψ_b) =>
    rw [witnessSetTaken.eq_7] at hw ⊢
    exact witnessSetTaken_disj_one_mono S_Ψ σ _ (by exact not_and_or.mp hsat) ψ_L ψ_R hw
  | .neg (.disj ψ_a ψ_b) =>
    rw [witnessSetTaken.eq_8] at hw ⊢
    exact witnessSetTaken_disj_one_mono S_Ψ σ _ (by exact not_or.mp hsat) ψ_L ψ_R hw
  | .neg (.neg ψ') =>
    rw [witnessSetTaken.eq_9] at hw ⊢
    exact witnessSetTaken_disj_one_mono S_Ψ σ ψ' (by exact not_not.mp hsat) ψ_L ψ_R hw
termination_by ψ.weight
decreasing_by all_goals (simp only [Formula.weight]; omega)

/-! ## Dep-closure helper -/

private lemma encodeNNF_dep_closure [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (Y_x : X → Finset Y)
    (S_Ψ : Finset (Package N V)) (σ : X → Y)
    (hσ_dom : ∀ x, σ x ∈ Y_x x)
    (CW : Finset (Package N' V'))
    (mem_embed : ∀ p, p ∈ S_Ψ → embedPkg (X := X) (Y := Y) p ∈ CW)
    (mem_var : ∀ x, (hvn.varN x, hvv.varValV (σ x)) ∈ CW)
    (hCW_orig : ∀ n v, (hvn.origN n, v) ∈ CW →
        ∃ p ∈ S_Ψ, embedPkg (X := X) (Y := Y) p = (hvn.origN n, v))
    (hCW_disj_zero : ∀ ψ_L ψ_R, (hvn.disjunctN ψ_L ψ_R, hvv.zeroV) ∈ CW →
        (ψ_L.satisfies S_Ψ σ) ∧
          witnessSetTaken (N' := N') (V' := V') S_Ψ σ ψ_L ⊆ CW ∧
          witnessSetUntaken S_Ψ ψ_R ⊆ CW)
    (hCW_disj_one : ∀ ψ_L ψ_R, (hvn.disjunctN ψ_L ψ_R, hvv.oneV) ∈ CW →
        (ψ_R.satisfies S_Ψ σ) ∧
          witnessSetUntaken (N' := N') (V' := V') S_Ψ ψ_L ⊆ CW ∧
          witnessSetTaken S_Ψ σ ψ_R ⊆ CW)
    (q₀ : Package N' V')
    (ψ : Formula N V X Y)
    (hwit : (q₀ ∉ CW ∧ witnessSetUntaken (N' := N') (V' := V') S_Ψ ψ ⊆ CW) ∨
            ((ψ.satisfies S_Ψ σ) ∧ witnessSetTaken S_Ψ σ ψ ⊆ CW))
    (q : Package N' V')
    (m : N') (vs : Finset V')
    (henc : (q, m, vs) ∈ encodeNNF Y_x q₀ ψ)
    (hq : q ∈ CW) :
    ∃ v ∈ vs, (m, v) ∈ CW := by
  match ψ with
  | .dep n dvs =>
    simp only [encodeNNF, Finset.mem_singleton, Prod.mk.injEq] at henc
    obtain ⟨rfl, rfl, rfl⟩ := henc
    rcases hwit with ⟨hq₀, _⟩ | ⟨hsat, _⟩
    · exact absurd hq hq₀
    · obtain ⟨v, hv, hvS⟩ := hsat
      exact ⟨hvv.origV v, Finset.mem_map.mpr ⟨v, hv, rfl⟩, mem_embed _ hvS⟩
  | .conj ψ_L ψ_R =>
    simp only [encodeNNF, Finset.mem_union] at henc
    rcases henc with hL | hR
    · have hwit' : (q₀ ∉ CW ∧ witnessSetUntaken (N' := N') (V' := V') S_Ψ ψ_L ⊆ CW) ∨
          ((ψ_L.satisfies S_Ψ σ) ∧ witnessSetTaken S_Ψ σ ψ_L ⊆ CW) := by
        rcases hwit with ⟨hq₀, hu⟩ | ⟨hsat, ht⟩
        · exact Or.inl ⟨hq₀, fun x hx => hu (by simp [witnessSetUntaken.eq_2]; exact Or.inl hx)⟩
        · exact Or.inr ⟨hsat.1, fun x hx => ht (by simp [witnessSetTaken.eq_2]; exact Or.inl hx)⟩
      exact encodeNNF_dep_closure Y_x S_Ψ σ hσ_dom CW mem_embed mem_var hCW_orig hCW_disj_zero hCW_disj_one
        q₀ ψ_L hwit' q m vs hL hq
    · have hwit' : (q₀ ∉ CW ∧ witnessSetUntaken (N' := N') (V' := V') S_Ψ ψ_R ⊆ CW) ∨
          ((ψ_R.satisfies S_Ψ σ) ∧ witnessSetTaken S_Ψ σ ψ_R ⊆ CW) := by
        rcases hwit with ⟨hq₀, hu⟩ | ⟨hsat, ht⟩
        · exact Or.inl ⟨hq₀, fun x hx => hu (by simp [witnessSetUntaken.eq_2]; exact Or.inr hx)⟩
        · exact Or.inr ⟨hsat.2, fun x hx => ht (by simp [witnessSetTaken.eq_2]; exact Or.inr hx)⟩
      exact encodeNNF_dep_closure Y_x S_Ψ σ hσ_dom CW mem_embed mem_var hCW_orig hCW_disj_zero hCW_disj_one
        q₀ ψ_R hwit' q m vs hR hq
  | .disj ψ_L ψ_R =>
    rw [encodeNNF] at henc
    rw [Finset.mem_union, Finset.mem_union] at henc
    rcases henc with (hwrap | hbody) | hbody
    · -- wrapper edge
      simp only [Finset.mem_singleton, Prod.mk.injEq] at hwrap
      obtain ⟨rfl, rfl, rfl⟩ := hwrap
      rcases hwit with ⟨hq₀, _⟩ | ⟨hsat, hwit_t⟩
      · exact absurd hq hq₀
      · by_cases hψL_sat : ψ_L.satisfies S_Ψ σ
        · refine ⟨hvv.zeroV, Finset.mem_insert_self _ _, ?_⟩
          apply hwit_t; simp only [witnessSetTaken.eq_3, if_pos hψL_sat]
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
            (Finset.mem_singleton.mpr rfl))))
        · refine ⟨hvv.oneV, by simp [Finset.mem_insert], ?_⟩
          apply hwit_t; simp only [witnessSetTaken.eq_3, if_neg hψL_sat]
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
            (Finset.mem_singleton.mpr rfl))))
    · -- body ψ_L
      by_cases hq₀' : (hvn.disjunctN ψ_L ψ_R, hvv.zeroV) ∈ CW
      · obtain ⟨hsat_L, htL, _⟩ := hCW_disj_zero ψ_L ψ_R hq₀'
        exact encodeNNF_dep_closure Y_x S_Ψ σ hσ_dom CW mem_embed mem_var hCW_orig hCW_disj_zero hCW_disj_one
          _ ψ_L (Or.inr ⟨hsat_L, htL⟩) q m vs hbody hq
      · have hwL : witnessSetUntaken (N' := N') (V' := V') S_Ψ ψ_L ⊆ CW := by
          rcases hwit with ⟨_, hu⟩ | ⟨_, ht⟩
          · exact fun x hx => hu (by simp [witnessSetUntaken.eq_3]; exact Or.inl hx)
          · by_cases hψL_sat : ψ_L.satisfies S_Ψ σ
            · exfalso; apply hq₀'
              apply ht; simp only [witnessSetTaken.eq_3, if_pos hψL_sat]
              exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
                (Finset.mem_singleton.mpr rfl))))
            · exact fun x hx => ht (by
                simp only [witnessSetTaken.eq_3, if_neg hψL_sat]
                exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hx))))
        exact encodeNNF_dep_closure Y_x S_Ψ σ hσ_dom CW mem_embed mem_var hCW_orig hCW_disj_zero hCW_disj_one
          _ ψ_L (Or.inl ⟨hq₀', hwL⟩) q m vs hbody hq
    · -- body ψ_R
      by_cases hq₀' : (hvn.disjunctN ψ_L ψ_R, hvv.oneV) ∈ CW
      · obtain ⟨hsat_R, _, htR⟩ := hCW_disj_one ψ_L ψ_R hq₀'
        exact encodeNNF_dep_closure Y_x S_Ψ σ hσ_dom CW mem_embed mem_var hCW_orig hCW_disj_zero hCW_disj_one
          _ ψ_R (Or.inr ⟨hsat_R, htR⟩) q m vs hbody hq
      · have hwR : witnessSetUntaken (N' := N') (V' := V') S_Ψ ψ_R ⊆ CW := by
          rcases hwit with ⟨_, hu⟩ | ⟨_, ht⟩
          · exact fun x hx => hu (by simp [witnessSetUntaken.eq_3]; exact Or.inr hx)
          · by_cases hψL_sat : ψ_L.satisfies S_Ψ σ
            · exact fun x hx => ht (by
                simp only [witnessSetTaken.eq_3, if_pos hψL_sat]
                exact Finset.mem_union.mpr (Or.inr hx))
            · exfalso; apply hq₀'
              apply ht; simp only [witnessSetTaken.eq_3, if_neg hψL_sat]
              exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
                (Finset.mem_singleton.mpr rfl))))
        exact encodeNNF_dep_closure Y_x S_Ψ σ hσ_dom CW mem_embed mem_var hCW_orig hCW_disj_zero hCW_disj_one
          _ ψ_R (Or.inl ⟨hq₀', hwR⟩) q m vs hbody hq
  | .varCmp x ω y =>
    simp only [encodeNNF, Finset.mem_singleton, Prod.mk.injEq] at henc
    obtain ⟨rfl, rfl, rfl⟩ := henc
    -- The encoded dependency is (q₀, varN x, cmpVersionSet (Y_x x) ω y).
    -- Witness: use σ x -- by hwit (taken or untaken from variable's sat),
    -- we need σ x ∈ cmpVersionSet, which requires ω.eval (σ x) y.
    -- This is exactly what `Formula.varCmp x ω y` being satisfied means.
    rcases hwit with ⟨hq₀, _⟩ | ⟨hsat, _⟩
    · exact absurd hq hq₀
    · refine ⟨hvv.varValV (σ x), ?_, mem_var x⟩
      rw [mem_cmpVersionSet]
      exact ⟨hσ_dom x, hsat⟩
  | .neg (.dep n dvs) =>
    simp only [encodeNNF, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Prod.mk.injEq] at henc
    rcases henc with ⟨rfl, rfl, rfl⟩ | ⟨u, hu, rfl, rfl, rfl⟩
    · rcases hwit with ⟨hq₀, _⟩ | ⟨_, hwit_t⟩
      · exact absurd hq hq₀
      · refine ⟨hvv.oneV, Finset.mem_singleton.mpr rfl, ?_⟩
        apply hwit_t; simp only [witnessSetTaken.eq_5]
        exact Finset.mem_singleton.mpr rfl
    · obtain ⟨⟨pn, pv⟩, hpS, hpeq⟩ := hCW_orig n (hvv.origV u) hq
      simp only [embedPkg, Prod.mk.injEq] at hpeq
      have h1 := hvn.origN.injective hpeq.1
      have h2 := hvv.origV.injective hpeq.2
      subst h1; subst h2
      rcases hwit with ⟨_, hwit_u⟩ | ⟨hsat, _⟩
      · refine ⟨hvv.zeroV, Finset.mem_singleton.mpr rfl, ?_⟩
        apply hwit_u; rw [witnessSetUntaken.eq_5]
        rw [if_pos (⟨pv, hu, hpS⟩ : ∃ u ∈ dvs, ((pn, u) : Package N V) ∈ S_Ψ)]
        exact Finset.mem_singleton.mpr rfl
      · exfalso; exact hsat ⟨pv, hu, hpS⟩
  | .neg (.varCmp x ω y) =>
    rw [encodeNNF.eq_6] at henc
    have hwit' := hwit.imp
      (And.imp_right fun hu => by rwa [witnessSetUntaken.eq_6] at hu)
      (And.imp (fun hsat => (complement_eval ω _ _).mpr hsat)
        (fun ht => by rwa [witnessSetTaken.eq_6] at ht))
    exact encodeNNF_dep_closure Y_x S_Ψ σ hσ_dom CW mem_embed mem_var hCW_orig hCW_disj_zero hCW_disj_one
      q₀ _ hwit' q m vs henc hq
  | .neg (.conj ψ_L ψ_R) =>
    rw [encodeNNF.eq_7] at henc
    have hwit' := hwit.imp
      (And.imp_right fun hu => by rwa [witnessSetUntaken.eq_7] at hu)
      (And.imp (fun hsat => not_and_or.mp hsat)
        (fun ht => by rwa [witnessSetTaken.eq_7] at ht))
    exact encodeNNF_dep_closure Y_x S_Ψ σ hσ_dom CW mem_embed mem_var hCW_orig hCW_disj_zero hCW_disj_one
      q₀ _ hwit' q m vs henc hq
  | .neg (.disj ψ_L ψ_R) =>
    rw [encodeNNF.eq_8] at henc
    have hwit' := hwit.imp
      (And.imp_right fun hu => by rwa [witnessSetUntaken.eq_8] at hu)
      (And.imp (fun hsat => not_or.mp hsat)
        (fun ht => by rwa [witnessSetTaken.eq_8] at ht))
    exact encodeNNF_dep_closure Y_x S_Ψ σ hσ_dom CW mem_embed mem_var hCW_orig hCW_disj_zero hCW_disj_one
      q₀ _ hwit' q m vs henc hq
  | .neg (.neg ψ') =>
    rw [encodeNNF.eq_9] at henc
    have hwit' := hwit.imp
      (And.imp_right fun hu => by rwa [witnessSetUntaken.eq_9] at hu)
      (And.imp (fun hsat => not_not.mp hsat)
        (fun ht => by rwa [witnessSetTaken.eq_9] at ht))
    exact encodeNNF_dep_closure Y_x S_Ψ σ hσ_dom CW mem_embed mem_var hCW_orig hCW_disj_zero hCW_disj_one
      q₀ ψ' hwit' q m vs henc hq
termination_by ψ.weight
decreasing_by all_goals (simp only [Formula.weight]; omega)

/-! ## CW disjunct structure lemmas -/

private lemma completenessWitness_disj_zero [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)] [Fintype X]
    {S_Ψ : Finset (Package N V)} {Δ_Ψ : VFDepRel N V X Y} {σ : X → Y}
    (ψ_L ψ_R : Formula N V X Y)
    (hmem : (hvn.disjunctN ψ_L ψ_R, hvv.zeroV) ∈
      completenessWitness (N' := N') (V' := V') S_Ψ Δ_Ψ σ) :
    (ψ_L.satisfies S_Ψ σ) ∧
      witnessSetTaken (N' := N') (V' := V') S_Ψ σ ψ_L ⊆ completenessWitness S_Ψ Δ_Ψ σ ∧
      witnessSetUntaken S_Ψ ψ_R ⊆ completenessWitness S_Ψ Δ_Ψ σ := by
  -- Extract the formula witness producer
  unfold completenessWitness at hmem
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hmem
  rcases hmem with (⟨p, _, hp⟩ | ⟨⟨p, ψ⟩, hdep, hw⟩) | ⟨x, _, heq⟩
  · -- from embedPkg
    simp only [embedPkg, Prod.mk.injEq] at hp
    exact absurd hp.1.symm (hvn.disjunctN_ne_origN _ _ _)
  · -- from witnessSet
    split_ifs at hw with hpS
    · -- taken
      obtain ⟨hsat, h1, h2⟩ := witnessSetTaken_disj_zero_mono S_Ψ σ ψ ψ_L ψ_R hw
      refine ⟨hsat, ?_, ?_⟩
      · intro x hx
        unfold completenessWitness
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨⟨p, ψ⟩, hdep, by
          show x ∈ (if p ∈ S_Ψ then _ else _)
          rw [if_pos hpS]; exact h1 hx⟩
      · intro x hx
        unfold completenessWitness
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨⟨p, ψ⟩, hdep, by
          show x ∈ (if p ∈ S_Ψ then _ else _)
          rw [if_pos hpS]; exact h2 hx⟩
    · exact (witnessSetUntaken_disjunct_det S_Ψ ψ ψ_L ψ_R _ hw).elim
  · -- from variable packages: contradicts disjunctN ≠ varN
    simp only [Prod.mk.injEq] at heq
    exact absurd heq.1.symm (hvn.disjunctN_ne_varN _ _ _)

private lemma completenessWitness_disj_one [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)] [Fintype X]
    {R_Ψ : Real N V} {S_Ψ : Finset (Package N V)} {Δ_Ψ : VFDepRel N V X Y}
    {r : Package N V} {σ : X → Y}
    (hres : IsVFResolution R_Ψ Δ_Ψ r S_Ψ σ)
    (ψ_L ψ_R : Formula N V X Y)
    (hmem : (hvn.disjunctN ψ_L ψ_R, hvv.oneV) ∈
      completenessWitness (N' := N') (V' := V') S_Ψ Δ_Ψ σ) :
    (ψ_R.satisfies S_Ψ σ) ∧
      witnessSetUntaken (N' := N') (V' := V') S_Ψ ψ_L ⊆ completenessWitness S_Ψ Δ_Ψ σ ∧
      witnessSetTaken S_Ψ σ ψ_R ⊆ completenessWitness S_Ψ Δ_Ψ σ := by
  unfold completenessWitness at hmem
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hmem
  rcases hmem with (⟨p, _, hp⟩ | ⟨⟨p, ψ⟩, hdep, hw⟩) | ⟨x, _, heq⟩
  · simp only [embedPkg, Prod.mk.injEq] at hp
    exact absurd hp.1.symm (hvn.disjunctN_ne_origN _ _ _)
  · split_ifs at hw with hpS
    · have hsat : ψ.satisfies S_Ψ σ := hres.formula_closure p hpS ψ hdep
      obtain ⟨hsatR, h1, h2⟩ := witnessSetTaken_disj_one_mono S_Ψ σ ψ hsat ψ_L ψ_R hw
      refine ⟨hsatR, ?_, ?_⟩
      · intro x hx
        unfold completenessWitness
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨⟨p, ψ⟩, hdep, by
          show x ∈ (if p ∈ S_Ψ then _ else _)
          rw [if_pos hpS]; exact h1 hx⟩
      · intro x hx
        unfold completenessWitness
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨⟨p, ψ⟩, hdep, by
          show x ∈ (if p ∈ S_Ψ then _ else _)
          rw [if_pos hpS]; exact h2 hx⟩
    · exact (witnessSetUntaken_disjunct_det S_Ψ ψ ψ_L ψ_R _ hw).elim
  · simp only [Prod.mk.injEq] at heq
    exact absurd heq.1.symm (hvn.disjunctN_ne_varN _ _ _)

/-! ## Version pinning -/

private lemma witnessSet_version_pinning [DecidableEq N] [DecidableEq V] [DecidableEq X]
    [DecidableEq Y] [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    {R_Ψ : Real N V} {Δ_Ψ : VFDepRel N V X Y} {r : Package N V}
    {S_Ψ : Finset (Package N V)} {σ : X → Y}
    (hres : IsVFResolution R_Ψ Δ_Ψ r S_Ψ σ)
    {n : N'} {v₁ v₂ : V'}
    (h1 : ∃ p ψ, (p, ψ) ∈ Δ_Ψ ∧
      (n, v₁) ∈ (if p ∈ S_Ψ then witnessSetTaken (N' := N') (V' := V') S_Ψ σ ψ
                            else witnessSetUntaken S_Ψ ψ))
    (h2 : ∃ p ψ, (p, ψ) ∈ Δ_Ψ ∧
      (n, v₂) ∈ (if p ∈ S_Ψ then witnessSetTaken (N' := N') (V' := V') S_Ψ σ ψ
                            else witnessSetUntaken S_Ψ ψ)) :
    v₁ = v₂ := by
  obtain ⟨p₁, ψ₁, hd₁, hw₁⟩ := h1
  obtain ⟨p₂, ψ₂, hd₂, hw₂⟩ := h2
  match hsyn : hvn.trySyntheticN n with
  | some (n', vs) =>
    have hneq : n = hvn.syntheticN n' vs := (hvn.trySyntheticN_some _ _ hsyn).symm
    subst hneq
    have getv : ∀ {p ψ v}, (p, ψ) ∈ Δ_Ψ →
        (hvn.syntheticN n' vs, v) ∈
          (if p ∈ S_Ψ then witnessSetTaken (N' := N') (V' := V') S_Ψ σ ψ
                      else witnessSetUntaken S_Ψ ψ) →
        v = if ∃ u ∈ vs, ((n', u) : Package N V) ∈ S_Ψ then hvv.zeroV else hvv.oneV := by
      intro p ψ v hd hmem
      split at hmem
      · rename_i hpS
        have hsat : ψ.satisfies S_Ψ σ := hres.formula_closure p hpS ψ hd
        exact witnessSetTaken_negDep_det S_Ψ σ ψ hsat n' vs v hmem
      · have hv := witnessSetUntaken_negDep_det S_Ψ ψ n' vs v hmem
        have hex := witnessSetUntaken_negDep_exists S_Ψ ψ n' vs v hmem
        rw [hv, if_pos hex]
    rw [getv hd₁ hw₁, getv hd₂ hw₂]
  | none =>
    have hcls₁ : (∃ n' vs, n = hvn.syntheticN n' vs) ∨ (∃ ψ_L ψ_R, n = hvn.disjunctN ψ_L ψ_R) := by
      split at hw₁
      · exact witnessSetTaken_name_classify S_Ψ σ ψ₁ n v₁ hw₁
      · exact witnessSetUntaken_name_classify S_Ψ ψ₁ n v₁ hw₁
    rcases hcls₁ with ⟨n', vs, hn⟩ | ⟨ψ_L, ψ_R, hn⟩
    · subst hn
      simp [hvn.trySyntheticN_syntheticN] at hsyn
    · subst hn
      have getv : ∀ {p ψ v}, (p, ψ) ∈ Δ_Ψ →
          (hvn.disjunctN ψ_L ψ_R, v) ∈
            (if p ∈ S_Ψ then witnessSetTaken (N' := N') (V' := V') S_Ψ σ ψ
                        else witnessSetUntaken S_Ψ ψ) →
          v = if ψ_L.satisfies S_Ψ σ then hvv.zeroV else hvv.oneV := by
        intro p ψ v hd hmem
        split at hmem
        · exact witnessSetTaken_disjunct_det S_Ψ σ ψ ψ_L ψ_R v hmem
        · exact (witnessSetUntaken_disjunct_det S_Ψ ψ ψ_L ψ_R v hmem).elim
      rw [getv hd₁ hw₁, getv hd₂ hw₂]

/-! ## Main completeness theorem.

Mirrors PF: no `hΔ_cov`, no `hvu_wit`, no `p₀` plumbing -- just an
`IsVFResolution` hypothesis. -/

-- Paper Thm 4.6.5 (Variable Formula Reduction Completeness).
theorem varFormula_completeness
    [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
    [LT Y] [DecidableRel (· < · : Y → Y → Prop)] [Fintype X]
    (Y_x : X → Finset Y)
    (R_Ψ : Real N V) (Δ_Ψ : VFDepRel N V X Y)
    (r : Package N V) (σ : X → Y)
    (hσ_dom : ∀ x, σ x ∈ Y_x x)
    (S_Ψ : Finset (Package N V))
    (hres : IsVFResolution R_Ψ Δ_Ψ r S_Ψ σ) :
    IsResolution (vfReal (N' := N') (V' := V') Y_x R_Ψ Δ_Ψ)
      (vfDeps (N' := N') (V' := V') Y_x Δ_Ψ)
      (embedPkg (X := X) (Y := Y) r)
      (completenessWitness S_Ψ Δ_Ψ σ) := by
  -- Abbreviation
  set CW := completenessWitness S_Ψ Δ_Ψ σ with hCW_def
  -- Convenience: embedPkg p is in CW when p ∈ S_Ψ
  have mem_embed : ∀ p, p ∈ S_Ψ → embedPkg (X := X) (Y := Y) p ∈ CW := by
    intro p hp; show _ ∈ completenessWitness _ _ _; unfold completenessWitness
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ hp))
  -- Convenience: variable packages are in CW
  have mem_var : ∀ x, (hvn.varN x, hvv.varValV (σ x)) ∈ CW := by
    intro x; show _ ∈ completenessWitness _ _ _; unfold completenessWitness
    exact Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- subset
    intro q hq
    show q ∈ vfReal Y_x R_Ψ Δ_Ψ
    simp only [hCW_def, completenessWitness, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at hq
    rcases hq with (⟨p, hp, rfl⟩ | ⟨⟨p, ψ⟩, hdep, hw⟩) | hmem
    · -- from S_Ψ.image embedPkg
      unfold vfReal
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (hres.subset hp)))
    · -- from witnessSet
      unfold vfReal
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨⟨p, ψ⟩, hdep, by
        split at hw
        · exact witnessSetTaken_subset_witnessPackages S_Ψ σ _ ψ hw
        · exact witnessSetUntaken_subset_witnessPackages S_Ψ _ ψ hw⟩
    · -- from variable packages
      obtain ⟨x, _, rfl⟩ := hmem
      unfold vfReal
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _,
        Finset.mem_image_of_mem _ (hσ_dom x)⟩
  · -- root_mem
    exact mem_embed r hres.root_mem
  · -- dep_closure
    have hCW_orig : ∀ n v, (hvn.origN n, v) ∈ CW →
        ∃ p ∈ S_Ψ, embedPkg (X := X) (Y := Y) p = (hvn.origN n, v) := by
      intro n v hv
      simp only [hCW_def, completenessWitness, Finset.mem_union, Finset.mem_image,
        Finset.mem_biUnion] at hv
      rcases hv with (⟨p, hp, hpe⟩ | ⟨⟨p, ψ⟩, _, hw⟩) | ⟨x, _, heq⟩
      · exact ⟨p, hp, hpe⟩
      · split at hw
        · exact absurd hw (witnessSetTaken_not_orig S_Ψ σ ψ n _)
        · exact absurd hw (witnessSetUntaken_not_orig S_Ψ ψ n _)
      · simp only [Prod.mk.injEq] at heq
        exact absurd heq.1 (hvn.varN_ne_origN _ _)
    have hCW_disj_zero : ∀ ψ_L ψ_R, (hvn.disjunctN ψ_L ψ_R, hvv.zeroV) ∈ CW →
        (ψ_L.satisfies S_Ψ σ) ∧
          witnessSetTaken (N' := N') (V' := V') S_Ψ σ ψ_L ⊆ CW ∧
          witnessSetUntaken S_Ψ ψ_R ⊆ CW :=
      fun ψ_L ψ_R h => completenessWitness_disj_zero ψ_L ψ_R h
    have hCW_disj_one : ∀ ψ_L ψ_R, (hvn.disjunctN ψ_L ψ_R, hvv.oneV) ∈ CW →
        (ψ_R.satisfies S_Ψ σ) ∧
          witnessSetUntaken (N' := N') (V' := V') S_Ψ ψ_L ⊆ CW ∧
          witnessSetTaken S_Ψ σ ψ_R ⊆ CW :=
      fun ψ_L ψ_R h => completenessWitness_disj_one hres ψ_L ψ_R h
    intro q hq m vs' hd
    simp only [vfDeps, encode, Finset.mem_biUnion] at hd
    obtain ⟨⟨p, ψ⟩, hdep, henc⟩ := hd
    by_cases hp : p ∈ S_Ψ
    · have hsat : ψ.satisfies S_Ψ σ := hres.formula_closure p hp ψ hdep
      have hwit : witnessSetTaken (N' := N') (V' := V') S_Ψ σ ψ ⊆ CW := by
        intro x hx
        show x ∈ completenessWitness _ _ _
        unfold completenessWitness
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨⟨p, ψ⟩, hdep, by
          show x ∈ (if p ∈ S_Ψ then _ else _); rw [if_pos hp]; exact hx⟩
      exact encodeNNF_dep_closure Y_x S_Ψ σ hσ_dom CW mem_embed mem_var hCW_orig
        hCW_disj_zero hCW_disj_one (embedPkg p) ψ (Or.inr ⟨hsat, hwit⟩)
        q m vs' henc hq
    · have hwit : witnessSetUntaken (N' := N') (V' := V') S_Ψ ψ ⊆ CW := by
        intro x hx
        show x ∈ completenessWitness _ _ _
        unfold completenessWitness
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨⟨p, ψ⟩, hdep, by
          show x ∈ (if p ∈ S_Ψ then _ else _); rw [if_neg hp]; exact hx⟩
      have hq₀ : embedPkg (X := X) (Y := Y) p ∉ CW := by
        intro hmem
        apply hp
        have : (hvn.origN p.1, hvv.origV p.2) ∈ CW := by
          show embedPkg p ∈ _; exact hmem
        obtain ⟨p', hp', hpe⟩ := hCW_orig p.1 (hvv.origV p.2) this
        simp only [embedPkg, Prod.mk.injEq] at hpe
        have h1 := hvn.origN.injective hpe.1
        have h2 := hvv.origV.injective hpe.2
        cases p with | mk n v => cases p' with | mk n' v' =>
        simp at h1 h2; subst h1; subst h2; exact hp'
      exact encodeNNF_dep_closure Y_x S_Ψ σ hσ_dom CW mem_embed mem_var hCW_orig
        hCW_disj_zero hCW_disj_one (embedPkg p) ψ (Or.inl ⟨hq₀, hwit⟩)
        q m vs' henc hq
  · -- version_unique
    intro n v₁ v₂ hv₁ hv₂
    simp only [hCW_def, completenessWitness, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at hv₁ hv₂
    -- Three cases for each: original embed, witnessSet, or variable package.
    rcases hv₁ with (⟨p₁, hp₁, heq1⟩ | ⟨⟨p₁, ψ₁⟩, hd₁, hw₁⟩) | ⟨x₁, _, heq1⟩ <;>
    rcases hv₂ with (⟨p₂, hp₂, heq2⟩ | ⟨⟨p₂, ψ₂⟩, hd₂, hw₂⟩) | ⟨x₂, _, heq2⟩
    · -- both original
      obtain ⟨n₁, w₁⟩ := p₁; obtain ⟨n₂, w₂⟩ := p₂
      simp only [embedPkg, Prod.mk.injEq] at heq1 heq2
      obtain ⟨h1n, rfl⟩ := heq1; obtain ⟨h2n, rfl⟩ := heq2
      have := hvn.origN.injective (h1n.trans h2n.symm); subst this
      exact congrArg hvv.origV (hres.version_unique _ _ _ hp₁ hp₂)
    · -- v₁ from embedPkg, v₂ from witnessSet
      simp only [embedPkg, Prod.mk.injEq] at heq1
      obtain ⟨rfl, rfl⟩ := heq1
      split at hw₂
      · exact absurd hw₂ (witnessSetTaken_not_orig S_Ψ σ ψ₂ _ _)
      · exact absurd hw₂ (witnessSetUntaken_not_orig S_Ψ ψ₂ _ _)
    · -- v₁ from embedPkg, v₂ from variable: origN ≠ varN
      simp only [embedPkg, Prod.mk.injEq] at heq1
      simp only [Prod.mk.injEq] at heq2
      have : hvn.origN p₁.1 = hvn.varN x₂ := heq1.1.trans heq2.1.symm
      exact absurd this (hvn.origN_ne_varN _ _)
    · -- v₁ from witnessSet, v₂ from embedPkg
      simp only [embedPkg, Prod.mk.injEq] at heq2
      obtain ⟨rfl, rfl⟩ := heq2
      split at hw₁
      · exact absurd hw₁ (witnessSetTaken_not_orig S_Ψ σ ψ₁ _ _)
      · exact absurd hw₁ (witnessSetUntaken_not_orig S_Ψ ψ₁ _ _)
    · -- both witnessSet: use witnessSet_version_pinning
      exact witnessSet_version_pinning hres ⟨p₁, ψ₁, hd₁, hw₁⟩ ⟨p₂, ψ₂, hd₂, hw₂⟩
    · -- v₁ from witnessSet, v₂ from variable: n = varN x₂; witnessSet doesn't produce varN
      simp only [Prod.mk.injEq] at heq2
      obtain ⟨hneq, rfl⟩ := heq2
      rw [← hneq] at hw₁
      split at hw₁
      · exact absurd hw₁ (witnessSetTaken_not_varN S_Ψ σ ψ₁ _ _)
      · exact absurd hw₁ (witnessSetUntaken_not_varN S_Ψ ψ₁ _ _)
    · -- v₁ from variable, v₂ from embedPkg
      simp only [embedPkg, Prod.mk.injEq] at heq2
      simp only [Prod.mk.injEq] at heq1
      have : hvn.origN p₂.1 = hvn.varN x₁ := heq2.1.trans heq1.1.symm
      exact absurd this (hvn.origN_ne_varN _ _)
    · -- v₁ from variable, v₂ from witnessSet
      simp only [Prod.mk.injEq] at heq1
      obtain ⟨hneq, rfl⟩ := heq1
      rw [← hneq] at hw₂
      split at hw₂
      · exact absurd hw₂ (witnessSetTaken_not_varN S_Ψ σ ψ₂ _ _)
      · exact absurd hw₂ (witnessSetUntaken_not_varN S_Ψ ψ₂ _ _)
    · -- both variable: same name forces same x, so same version
      simp only [Prod.mk.injEq] at heq1 heq2
      obtain ⟨hn1, rfl⟩ := heq1; obtain ⟨hn2, rfl⟩ := heq2
      have hx : x₁ = x₂ := hvn.varN.injective (hn1.trans hn2.symm)
      rw [hx]

end PackageCalculus.VarFormula
