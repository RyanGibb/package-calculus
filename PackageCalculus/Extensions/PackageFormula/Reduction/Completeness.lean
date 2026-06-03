import PackageCalculus.Extensions.PackageFormula.Reduction.Definition

namespace PackageCalculus.PkgFormula

open Classical

variable {N : Type*} {V : Type*} {N' : Type*} {V' : Type*}
variable [DecidableEq N'] [DecidableEq V']
variable [hpn : HasPFNames N V N'] [hpv : Conflict.HasConflictVersions V V']

/-! ## Dual-context witness construction (paper's W^⊤ / W^⊥)

We define two functions:

* `witnessSetTaken S_Ψ ψ` -- witnesses for `ψ` on a *taken* path (the wrapper
  depender for the formula containing this subterm is in `S_Ψ`).

* `witnessSetUntaken S_Ψ ψ` -- witnesses for `ψ` on an *untaken* path (the
  wrapper depender is absent, so the wrapper-issued edges do not fire; but the
  *negation* edges fire from the original package `(n, u)` if `(n, u) ∈ S_Ψ`).

They are not mutually recursive -- `witnessSetTaken` calls `witnessSetUntaken`
in the disjunction case but not vice versa, so each is defined separately by
well-founded recursion on `Formula.weight`. -/

def witnessSetUntaken [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V)) :
    Formula N V → Finset (Package N' V')
  | .dep _ _ => ∅
  | .conj ψ_L ψ_R => witnessSetUntaken S_Ψ ψ_L ∪ witnessSetUntaken S_Ψ ψ_R
  | .disj ψ_L ψ_R => witnessSetUntaken S_Ψ ψ_L ∪ witnessSetUntaken S_Ψ ψ_R
  | .neg (.dep n vs) =>
    if ∃ u ∈ vs, ((n, u) : Package N V) ∈ S_Ψ
    then {(hpn.syntheticN n vs, hpv.zeroV)}
    else ∅
  | .neg (.conj ψ_L ψ_R) =>
    witnessSetUntaken S_Ψ (.disj (.neg ψ_L) (.neg ψ_R))
  | .neg (.disj ψ_L ψ_R) =>
    witnessSetUntaken S_Ψ (.conj (.neg ψ_L) (.neg ψ_R))
  | .neg (.neg ψ) =>
    witnessSetUntaken S_Ψ ψ
termination_by ψ => ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

def witnessSetTaken [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V)) :
    Formula N V → Finset (Package N' V')
  | .dep _ _ => ∅
  | .conj ψ_L ψ_R => witnessSetTaken S_Ψ ψ_L ∪ witnessSetTaken S_Ψ ψ_R
  | .disj ψ_L ψ_R =>
    if S_Ψ ⊨ ψ_L then
      {(hpn.disjunctN ψ_L ψ_R, hpv.zeroV)} ∪
        witnessSetTaken S_Ψ ψ_L ∪ witnessSetUntaken S_Ψ ψ_R
    else
      {(hpn.disjunctN ψ_L ψ_R, hpv.oneV)} ∪
        witnessSetUntaken S_Ψ ψ_L ∪ witnessSetTaken S_Ψ ψ_R
  | .neg (.dep n vs) => {(hpn.syntheticN n vs, hpv.oneV)}
  | .neg (.conj ψ_L ψ_R) =>
    witnessSetTaken S_Ψ (.disj (.neg ψ_L) (.neg ψ_R))
  | .neg (.disj ψ_L ψ_R) =>
    witnessSetTaken S_Ψ (.conj (.neg ψ_L) (.neg ψ_R))
  | .neg (.neg ψ) =>
    witnessSetTaken S_Ψ ψ
termination_by ψ => ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

def completenessWitness [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V)) (Δ_Ψ : PFDepRel N V) :
    Finset (Package N' V') :=
  S_Ψ.image embedPkg ∪
    Δ_Ψ.biUnion (fun ⟨p, ψ⟩ =>
      if p ∈ S_Ψ then witnessSetTaken S_Ψ ψ else witnessSetUntaken S_Ψ ψ)

/-! ## Equational lemmas (auto-unfolds for `simp`) -/

section UnfoldEqs
variable [DecidableEq N] [DecidableEq V] (S_Ψ : Finset (Package N V))

@[simp] lemma witnessSetTaken_dep (n : N) (vs : Finset V) :
    witnessSetTaken S_Ψ (.dep n vs) = (∅ : Finset (Package N' V')) :=
  witnessSetTaken.eq_1 S_Ψ n vs

@[simp] lemma witnessSetTaken_conj (ψ_L ψ_R : Formula N V) :
    (witnessSetTaken S_Ψ (.conj ψ_L ψ_R) : Finset (Package N' V')) =
      witnessSetTaken S_Ψ ψ_L ∪ witnessSetTaken S_Ψ ψ_R :=
  witnessSetTaken.eq_2 S_Ψ ψ_L ψ_R

@[simp] lemma witnessSetTaken_disj (ψ_L ψ_R : Formula N V) :
    (witnessSetTaken S_Ψ (.disj ψ_L ψ_R) : Finset (Package N' V')) =
      if S_Ψ ⊨ ψ_L then
        {(hpn.disjunctN ψ_L ψ_R, hpv.zeroV)} ∪
          witnessSetTaken S_Ψ ψ_L ∪ witnessSetUntaken S_Ψ ψ_R
      else
        {(hpn.disjunctN ψ_L ψ_R, hpv.oneV)} ∪
          witnessSetUntaken S_Ψ ψ_L ∪ witnessSetTaken S_Ψ ψ_R :=
  witnessSetTaken.eq_3 S_Ψ ψ_L ψ_R

@[simp] lemma witnessSetTaken_neg_dep (n : N) (vs : Finset V) :
    (witnessSetTaken S_Ψ (.neg (.dep n vs)) : Finset (Package N' V')) =
      {(hpn.syntheticN n vs, hpv.oneV)} :=
  witnessSetTaken.eq_4 S_Ψ n vs

lemma witnessSetTaken_neg_conj (ψ_L ψ_R : Formula N V) :
    (witnessSetTaken S_Ψ (.neg (.conj ψ_L ψ_R)) : Finset (Package N' V')) =
      witnessSetTaken S_Ψ (.disj (.neg ψ_L) (.neg ψ_R)) :=
  witnessSetTaken.eq_5 S_Ψ ψ_L ψ_R

lemma witnessSetTaken_neg_disj (ψ_L ψ_R : Formula N V) :
    (witnessSetTaken S_Ψ (.neg (.disj ψ_L ψ_R)) : Finset (Package N' V')) =
      witnessSetTaken S_Ψ (.conj (.neg ψ_L) (.neg ψ_R)) :=
  witnessSetTaken.eq_6 S_Ψ ψ_L ψ_R

lemma witnessSetTaken_neg_neg (ψ : Formula N V) :
    (witnessSetTaken S_Ψ (.neg (.neg ψ)) : Finset (Package N' V')) =
      witnessSetTaken S_Ψ ψ :=
  witnessSetTaken.eq_7 S_Ψ ψ

@[simp] lemma witnessSetUntaken_dep (n : N) (vs : Finset V) :
    witnessSetUntaken S_Ψ (.dep n vs) = (∅ : Finset (Package N' V')) :=
  witnessSetUntaken.eq_1 S_Ψ n vs

@[simp] lemma witnessSetUntaken_conj (ψ_L ψ_R : Formula N V) :
    (witnessSetUntaken S_Ψ (.conj ψ_L ψ_R) : Finset (Package N' V')) =
      witnessSetUntaken S_Ψ ψ_L ∪ witnessSetUntaken S_Ψ ψ_R :=
  witnessSetUntaken.eq_2 S_Ψ ψ_L ψ_R

@[simp] lemma witnessSetUntaken_disj (ψ_L ψ_R : Formula N V) :
    (witnessSetUntaken S_Ψ (.disj ψ_L ψ_R) : Finset (Package N' V')) =
      witnessSetUntaken S_Ψ ψ_L ∪ witnessSetUntaken S_Ψ ψ_R :=
  witnessSetUntaken.eq_3 S_Ψ ψ_L ψ_R

@[simp] lemma witnessSetUntaken_neg_dep (n : N) (vs : Finset V) :
    (witnessSetUntaken S_Ψ (.neg (.dep n vs)) : Finset (Package N' V')) =
      if ∃ u ∈ vs, ((n, u) : Package N V) ∈ S_Ψ
      then {(hpn.syntheticN n vs, hpv.zeroV)}
      else ∅ :=
  witnessSetUntaken.eq_4 S_Ψ n vs

lemma witnessSetUntaken_neg_conj (ψ_L ψ_R : Formula N V) :
    (witnessSetUntaken S_Ψ (.neg (.conj ψ_L ψ_R)) : Finset (Package N' V')) =
      witnessSetUntaken S_Ψ (.disj (.neg ψ_L) (.neg ψ_R)) :=
  witnessSetUntaken.eq_5 S_Ψ ψ_L ψ_R

lemma witnessSetUntaken_neg_disj (ψ_L ψ_R : Formula N V) :
    (witnessSetUntaken S_Ψ (.neg (.disj ψ_L ψ_R)) : Finset (Package N' V')) =
      witnessSetUntaken S_Ψ (.conj (.neg ψ_L) (.neg ψ_R)) :=
  witnessSetUntaken.eq_6 S_Ψ ψ_L ψ_R

lemma witnessSetUntaken_neg_neg (ψ : Formula N V) :
    (witnessSetUntaken S_Ψ (.neg (.neg ψ)) : Finset (Package N' V')) =
      witnessSetUntaken S_Ψ ψ :=
  witnessSetUntaken.eq_7 S_Ψ ψ

end UnfoldEqs

/-! ## No original-name witnesses -/

lemma witnessSetUntaken_not_orig [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V) (n : N) (v : V') :
    (hpn.origN n, v) ∉ witnessSetUntaken S_Ψ ψ := by
  match ψ with
  | .dep _ _ => simp
  | .conj ψ_L ψ_R =>
    simp only [witnessSetUntaken_conj, Finset.mem_union, not_or]
    exact ⟨witnessSetUntaken_not_orig S_Ψ ψ_L n v,
           witnessSetUntaken_not_orig S_Ψ ψ_R n v⟩
  | .disj ψ_L ψ_R =>
    simp only [witnessSetUntaken_disj, Finset.mem_union, not_or]
    exact ⟨witnessSetUntaken_not_orig S_Ψ ψ_L n v,
           witnessSetUntaken_not_orig S_Ψ ψ_R n v⟩
  | .neg (.dep _ _) =>
    simp only [witnessSetUntaken_neg_dep]
    split
    · simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]
      intro h; exact absurd h (hpn.origN_ne_syntheticN _ _ _)
    · simp
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetUntaken_neg_conj]
    exact witnessSetUntaken_not_orig S_Ψ (.disj (.neg ψ_L) (.neg ψ_R)) n v
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetUntaken_neg_disj]
    exact witnessSetUntaken_not_orig S_Ψ (.conj (.neg ψ_L) (.neg ψ_R)) n v
  | .neg (.neg ψ') =>
    rw [witnessSetUntaken_neg_neg]
    exact witnessSetUntaken_not_orig S_Ψ ψ' n v
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

lemma witnessSetTaken_not_orig [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V) (n : N) (v : V') :
    (hpn.origN n, v) ∉ witnessSetTaken S_Ψ ψ := by
  match ψ with
  | .dep _ _ => simp
  | .conj ψ_L ψ_R =>
    simp only [witnessSetTaken_conj, Finset.mem_union, not_or]
    exact ⟨witnessSetTaken_not_orig S_Ψ ψ_L n v,
           witnessSetTaken_not_orig S_Ψ ψ_R n v⟩
  | .disj ψ_L ψ_R =>
    simp only [witnessSetTaken_disj]
    split
    · simp only [Finset.mem_union, Finset.mem_singleton, not_or]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro hsing
        have := (Prod.mk.injEq _ _ _ _).mp hsing
        exact absurd this.1 (hpn.origN_ne_disjunctN _ _ _)
      · exact witnessSetTaken_not_orig S_Ψ ψ_L n v
      · exact witnessSetUntaken_not_orig S_Ψ ψ_R n v
    · simp only [Finset.mem_union, Finset.mem_singleton, not_or]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro hsing
        have := (Prod.mk.injEq _ _ _ _).mp hsing
        exact absurd this.1 (hpn.origN_ne_disjunctN _ _ _)
      · exact witnessSetUntaken_not_orig S_Ψ ψ_L n v
      · exact witnessSetTaken_not_orig S_Ψ ψ_R n v
  | .neg (.dep _ _) =>
    simp only [witnessSetTaken_neg_dep, Finset.mem_singleton, Prod.mk.injEq, not_and]
    intro h; exact absurd h (hpn.origN_ne_syntheticN _ _ _)
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetTaken_neg_conj]
    exact witnessSetTaken_not_orig S_Ψ (.disj (.neg ψ_L) (.neg ψ_R)) n v
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetTaken_neg_disj]
    exact witnessSetTaken_not_orig S_Ψ (.conj (.neg ψ_L) (.neg ψ_R)) n v
  | .neg (.neg ψ') =>
    rw [witnessSetTaken_neg_neg]
    exact witnessSetTaken_not_orig S_Ψ ψ' n v
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

/-! ## Version determinism (untaken side: always zeroV)

The untaken side has a clean determinism: any synthetic-N witness has version
zeroV.  Disjunct names never appear at all. -/

lemma witnessSetUntaken_negDep_det [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V) (n : N) (vs : Finset V) (v : V')
    (h : (hpn.syntheticN n vs, v) ∈ witnessSetUntaken S_Ψ ψ) :
    v = hpv.zeroV := by
  match ψ with
  | .dep _ _ => simp at h
  | .conj ψ_L ψ_R =>
    simp only [witnessSetUntaken_conj, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_negDep_det S_Ψ ψ_L n vs v)
      (witnessSetUntaken_negDep_det S_Ψ ψ_R n vs v)
  | .disj ψ_L ψ_R =>
    simp only [witnessSetUntaken_disj, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_negDep_det S_Ψ ψ_L n vs v)
      (witnessSetUntaken_negDep_det S_Ψ ψ_R n vs v)
  | .neg (.dep n' vs') =>
    simp only [witnessSetUntaken_neg_dep] at h
    split at h
    · simp only [Finset.mem_singleton, Prod.mk.injEq] at h
      exact h.2
    · simp at h
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetUntaken_neg_conj] at h
    exact witnessSetUntaken_negDep_det S_Ψ (.disj (.neg ψ_L) (.neg ψ_R)) n vs v h
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetUntaken_neg_disj] at h
    exact witnessSetUntaken_negDep_det S_Ψ (.conj (.neg ψ_L) (.neg ψ_R)) n vs v h
  | .neg (.neg ψ') =>
    rw [witnessSetUntaken_neg_neg] at h
    exact witnessSetUntaken_negDep_det S_Ψ ψ' n vs v h
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

lemma witnessSetUntaken_disjunct_det [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V) (ψ_L ψ_R : Formula N V) (v : V')
    (h : (hpn.disjunctN ψ_L ψ_R, v) ∈ witnessSetUntaken S_Ψ ψ) : False := by
  match ψ with
  | .dep _ _ => simp at h
  | .conj ψ_a ψ_b =>
    simp only [witnessSetUntaken_conj, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_disjunct_det S_Ψ ψ_a ψ_L ψ_R v)
      (witnessSetUntaken_disjunct_det S_Ψ ψ_b ψ_L ψ_R v)
  | .disj ψ_a ψ_b =>
    simp only [witnessSetUntaken_disj, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_disjunct_det S_Ψ ψ_a ψ_L ψ_R v)
      (witnessSetUntaken_disjunct_det S_Ψ ψ_b ψ_L ψ_R v)
  | .neg (.dep _ _) =>
    simp only [witnessSetUntaken_neg_dep] at h
    split at h
    · simp only [Finset.mem_singleton, Prod.mk.injEq] at h
      exact absurd h.1 (hpn.disjunctN_ne_syntheticN _ _ _ _)
    · simp at h
  | .neg (.conj ψ_a ψ_b) =>
    rw [witnessSetUntaken_neg_conj] at h
    exact witnessSetUntaken_disjunct_det S_Ψ (.disj (.neg ψ_a) (.neg ψ_b)) ψ_L ψ_R v h
  | .neg (.disj ψ_a ψ_b) =>
    rw [witnessSetUntaken_neg_disj] at h
    exact witnessSetUntaken_disjunct_det S_Ψ (.conj (.neg ψ_a) (.neg ψ_b)) ψ_L ψ_R v h
  | .neg (.neg ψ') =>
    rw [witnessSetUntaken_neg_neg] at h
    exact witnessSetUntaken_disjunct_det S_Ψ ψ' ψ_L ψ_R v h
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

/-! ## Disjunct version determinism (taken side)

For the disjunct names, taken-side version is determined by satisfaction of
the left disjunct -- and untaken never produces disjunct names, so this is
unconditional. -/

lemma witnessSetTaken_disjunct_det [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V) (ψ_L ψ_R : Formula N V) (v : V')
    (h : (hpn.disjunctN ψ_L ψ_R, v) ∈ witnessSetTaken S_Ψ ψ) :
    v = if S_Ψ ⊨ ψ_L then hpv.zeroV else hpv.oneV := by
  match ψ with
  | .dep _ _ => simp at h
  | .conj ψ_a ψ_b =>
    simp only [witnessSetTaken_conj, Finset.mem_union] at h
    exact h.elim
      (witnessSetTaken_disjunct_det S_Ψ ψ_a ψ_L ψ_R v)
      (witnessSetTaken_disjunct_det S_Ψ ψ_b ψ_L ψ_R v)
  | .disj ψ_a ψ_b =>
    simp only [witnessSetTaken_disj] at h
    split at h
    · rename_i hψa_sat
      simp only [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with (hsing | hL) | hU
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        obtain ⟨rfl, rfl⟩ := hpn.disjunctN_injective heq.1
        simp [hψa_sat, heq.2]
      · exact witnessSetTaken_disjunct_det S_Ψ ψ_a ψ_L ψ_R v hL
      · exact (witnessSetUntaken_disjunct_det S_Ψ ψ_b ψ_L ψ_R v hU).elim
    · rename_i hψa_unsat
      simp only [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with (hsing | hU) | hR
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        obtain ⟨rfl, rfl⟩ := hpn.disjunctN_injective heq.1
        simp [hψa_unsat, heq.2]
      · exact (witnessSetUntaken_disjunct_det S_Ψ ψ_a ψ_L ψ_R v hU).elim
      · exact witnessSetTaken_disjunct_det S_Ψ ψ_b ψ_L ψ_R v hR
  | .neg (.dep _ _) =>
    simp only [witnessSetTaken_neg_dep, Finset.mem_singleton, Prod.mk.injEq] at h
    exact absurd h.1 (hpn.disjunctN_ne_syntheticN _ _ _ _)
  | .neg (.conj ψ_a ψ_b) =>
    rw [witnessSetTaken_neg_conj] at h
    exact witnessSetTaken_disjunct_det S_Ψ (.disj (.neg ψ_a) (.neg ψ_b)) ψ_L ψ_R v h
  | .neg (.disj ψ_a ψ_b) =>
    rw [witnessSetTaken_neg_disj] at h
    exact witnessSetTaken_disjunct_det S_Ψ (.conj (.neg ψ_a) (.neg ψ_b)) ψ_L ψ_R v h
  | .neg (.neg ψ') =>
    rw [witnessSetTaken_neg_neg] at h
    exact witnessSetTaken_disjunct_det S_Ψ ψ' ψ_L ψ_R v h
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

/-! ## Subset of `witnessPackages` -/

lemma witnessSetUntaken_subset_witnessPackages [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V)) (p : Package N' V')
    (ψ : Formula N V) : witnessSetUntaken S_Ψ ψ ⊆ witnessPackages p ψ := by
  intro q hq
  match ψ with
  | .dep _ _ => simp at hq
  | .conj ψ_L ψ_R =>
    simp only [witnessSetUntaken_conj, Finset.mem_union] at hq
    simp only [witnessPackages, Finset.mem_union]
    exact hq.elim
      (fun h => Or.inl (witnessSetUntaken_subset_witnessPackages S_Ψ p ψ_L h))
      (fun h => Or.inr (witnessSetUntaken_subset_witnessPackages S_Ψ p ψ_R h))
  | .disj ψ_L ψ_R =>
    simp only [witnessSetUntaken_disj, Finset.mem_union] at hq
    have hunfold : witnessPackages p (.disj ψ_L ψ_R) =
        {(hpn.disjunctN ψ_L ψ_R, hpv.zeroV), (hpn.disjunctN ψ_L ψ_R, hpv.oneV)} ∪
        witnessPackages (hpn.disjunctN ψ_L ψ_R, hpv.zeroV) ψ_L ∪
        witnessPackages (hpn.disjunctN ψ_L ψ_R, hpv.oneV) ψ_R := by
      simp [witnessPackages]
    rw [hunfold]
    rcases hq with hL | hR
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
        (witnessSetUntaken_subset_witnessPackages S_Ψ _ ψ_L hL))))
    · exact Finset.mem_union.mpr (Or.inr
        (witnessSetUntaken_subset_witnessPackages S_Ψ _ ψ_R hR))
  | .neg (.dep n vs) =>
    simp only [witnessSetUntaken_neg_dep] at hq
    simp only [witnessPackages, Finset.mem_insert, Finset.mem_singleton]
    split at hq
    · simp only [Finset.mem_singleton] at hq
      exact Or.inl hq
    · simp at hq
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetUntaken_neg_conj] at hq
    have key : witnessPackages p (.neg (.conj ψ_L ψ_R)) =
        witnessPackages p (.disj (.neg ψ_L) (.neg ψ_R)) := by simp [witnessPackages]
    rw [key]
    exact witnessSetUntaken_subset_witnessPackages S_Ψ p (.disj (.neg ψ_L) (.neg ψ_R)) hq
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetUntaken_neg_disj] at hq
    have key : witnessPackages p (.neg (.disj ψ_L ψ_R)) =
        witnessPackages p (.conj (.neg ψ_L) (.neg ψ_R)) := by simp [witnessPackages]
    rw [key]
    exact witnessSetUntaken_subset_witnessPackages S_Ψ p (.conj (.neg ψ_L) (.neg ψ_R)) hq
  | .neg (.neg ψ') =>
    rw [witnessSetUntaken_neg_neg] at hq
    have key : witnessPackages p (.neg (.neg ψ')) = witnessPackages p ψ' := by
      simp [witnessPackages]
    rw [key]
    exact witnessSetUntaken_subset_witnessPackages S_Ψ p ψ' hq
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

lemma witnessSetTaken_subset_witnessPackages [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V)) (p : Package N' V')
    (ψ : Formula N V) : witnessSetTaken S_Ψ ψ ⊆ witnessPackages p ψ := by
  intro q hq
  match ψ with
  | .dep _ _ => simp at hq
  | .conj ψ_L ψ_R =>
    simp only [witnessSetTaken_conj, Finset.mem_union] at hq
    simp only [witnessPackages, Finset.mem_union]
    exact hq.elim
      (fun h => Or.inl (witnessSetTaken_subset_witnessPackages S_Ψ p ψ_L h))
      (fun h => Or.inr (witnessSetTaken_subset_witnessPackages S_Ψ p ψ_R h))
  | .disj ψ_L ψ_R =>
    have hunfold : witnessPackages p (.disj ψ_L ψ_R) =
        {(hpn.disjunctN ψ_L ψ_R, hpv.zeroV), (hpn.disjunctN ψ_L ψ_R, hpv.oneV)} ∪
        witnessPackages (hpn.disjunctN ψ_L ψ_R, hpv.zeroV) ψ_L ∪
        witnessPackages (hpn.disjunctN ψ_L ψ_R, hpv.oneV) ψ_R := by
      simp [witnessPackages]
    rw [hunfold]
    simp only [witnessSetTaken_disj] at hq
    split at hq
    · simp only [Finset.mem_union, Finset.mem_singleton] at hq
      rcases hq with (rfl | hL) | hU
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
          (Finset.mem_insert.mpr (Or.inl rfl)))))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
          (witnessSetTaken_subset_witnessPackages S_Ψ _ ψ_L hL))))
      · exact Finset.mem_union.mpr (Or.inr
          (witnessSetUntaken_subset_witnessPackages S_Ψ _ ψ_R hU))
    · simp only [Finset.mem_union, Finset.mem_singleton] at hq
      rcases hq with (rfl | hU) | hR
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
          (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))))))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
          (witnessSetUntaken_subset_witnessPackages S_Ψ _ ψ_L hU))))
      · exact Finset.mem_union.mpr (Or.inr
          (witnessSetTaken_subset_witnessPackages S_Ψ _ ψ_R hR))
  | .neg (.dep n vs) =>
    simp only [witnessSetTaken_neg_dep, Finset.mem_singleton] at hq
    subst hq
    simp [witnessPackages]
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetTaken_neg_conj] at hq
    have key : witnessPackages p (.neg (.conj ψ_L ψ_R)) =
        witnessPackages p (.disj (.neg ψ_L) (.neg ψ_R)) := by simp [witnessPackages]
    rw [key]
    exact witnessSetTaken_subset_witnessPackages S_Ψ p (.disj (.neg ψ_L) (.neg ψ_R)) hq
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetTaken_neg_disj] at hq
    have key : witnessPackages p (.neg (.disj ψ_L ψ_R)) =
        witnessPackages p (.conj (.neg ψ_L) (.neg ψ_R)) := by simp [witnessPackages]
    rw [key]
    exact witnessSetTaken_subset_witnessPackages S_Ψ p (.conj (.neg ψ_L) (.neg ψ_R)) hq
  | .neg (.neg ψ') =>
    rw [witnessSetTaken_neg_neg] at hq
    have key : witnessPackages p (.neg (.neg ψ')) = witnessPackages p ψ' := by
      simp [witnessPackages]
    rw [key]
    exact witnessSetTaken_subset_witnessPackages S_Ψ p ψ' hq
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

/-! ## Satisfaction-aware taken syntheticN witness invariant

Under the hypothesis `S_Ψ ⊨ ψ`, every `(syntheticN n vs, v)` in
`witnessSetTaken S_Ψ ψ` has version uniquely determined by `S_Ψ`:
  - zeroV when ∃ u ∈ vs, (n, u) ∈ S_Ψ  (from a recursed untaken-side path)
  - oneV  otherwise                    (from a taken-side path)

These cases are mutually exclusive, giving version uniqueness across the
whole `completenessWitness` set. -/

/-- Untaken-side synthetic witness implies some `(n, u) ∈ S_Ψ`. -/
lemma witnessSetUntaken_negDep_exists [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V) (n : N) (vs : Finset V) (v : V')
    (h : (hpn.syntheticN n vs, v) ∈ witnessSetUntaken S_Ψ ψ) :
    ∃ u ∈ vs, ((n, u) : Package N V) ∈ S_Ψ := by
  match ψ with
  | .dep _ _ => simp at h
  | .conj ψ_L ψ_R =>
    simp only [witnessSetUntaken_conj, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_negDep_exists S_Ψ ψ_L n vs v)
      (witnessSetUntaken_negDep_exists S_Ψ ψ_R n vs v)
  | .disj ψ_L ψ_R =>
    simp only [witnessSetUntaken_disj, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_negDep_exists S_Ψ ψ_L n vs v)
      (witnessSetUntaken_negDep_exists S_Ψ ψ_R n vs v)
  | .neg (.dep n' vs') =>
    simp only [witnessSetUntaken_neg_dep] at h
    split at h
    · rename_i hex
      simp only [Finset.mem_singleton] at h
      have heq := (Prod.mk.injEq _ _ _ _).mp h
      obtain ⟨rfl, rfl⟩ := hpn.syntheticN_injective heq.1
      exact hex
    · simp at h
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetUntaken_neg_conj] at h
    exact witnessSetUntaken_negDep_exists S_Ψ (.disj (.neg ψ_L) (.neg ψ_R)) n vs v h
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetUntaken_neg_disj] at h
    exact witnessSetUntaken_negDep_exists S_Ψ (.conj (.neg ψ_L) (.neg ψ_R)) n vs v h
  | .neg (.neg ψ') =>
    rw [witnessSetUntaken_neg_neg] at h
    exact witnessSetUntaken_negDep_exists S_Ψ ψ' n vs v h
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

/-- **Master version determinism for taken-side syntheticN witnesses.**

Under `S_Ψ ⊨ ψ`, the version of any syntheticN witness in `witnessSetTaken S_Ψ ψ`
is uniquely determined by whether the original package family has a member in `S_Ψ`:
- if `∃ u ∈ vs, (n, u) ∈ S_Ψ`, the version is `zeroV` (from a cross-recursed
  untaken-side `.neg (.dep n vs)`);
- otherwise, the version is `oneV` (from a taken-side `.neg (.dep n vs)` on the
  satisfaction tree of `ψ`). -/
lemma witnessSetTaken_negDep_det [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V) (hsat : S_Ψ ⊨ ψ)
    (n : N) (vs : Finset V) (v : V')
    (h : (hpn.syntheticN n vs, v) ∈ witnessSetTaken S_Ψ ψ) :
    v = if ∃ u ∈ vs, ((n, u) : Package N V) ∈ S_Ψ then hpv.zeroV else hpv.oneV := by
  match ψ with
  | .dep _ _ => simp at h
  | .conj ψ_L ψ_R =>
    simp only [witnessSetTaken_conj, Finset.mem_union] at h
    rcases h with hL | hR
    · exact witnessSetTaken_negDep_det S_Ψ ψ_L hsat.1 n vs v hL
    · exact witnessSetTaken_negDep_det S_Ψ ψ_R hsat.2 n vs v hR
  | .disj ψ_L ψ_R =>
    simp only [witnessSetTaken_disj] at h
    split at h
    · rename_i hψL_sat
      simp only [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with (hsing | hL) | hU
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        exact absurd heq.1 (hpn.syntheticN_ne_disjunctN _ _ _ _)
      · exact witnessSetTaken_negDep_det S_Ψ ψ_L hψL_sat n vs v hL
      · -- hU : (synth, v) ∈ wsU ψ_R. By untaken det, v = zeroV; by untaken_exists,
        --   ∃ u ∈ vs, (n, u) ∈ S_Ψ.
        have hv := witnessSetUntaken_negDep_det S_Ψ ψ_R n vs v hU
        have hex := witnessSetUntaken_negDep_exists S_Ψ ψ_R n vs v hU
        simp [hv, hex]
    · rename_i hψL_unsat
      simp only [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with (hsing | hU) | hR
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        exact absurd heq.1 (hpn.syntheticN_ne_disjunctN _ _ _ _)
      · have hv := witnessSetUntaken_negDep_det S_Ψ ψ_L n vs v hU
        have hex := witnessSetUntaken_negDep_exists S_Ψ ψ_L n vs v hU
        simp [hv, hex]
      · exact witnessSetTaken_negDep_det S_Ψ ψ_R (hsat.resolve_left hψL_unsat) n vs v hR
  | .neg (.dep n' vs') =>
    simp only [witnessSetTaken_neg_dep, Finset.mem_singleton] at h
    have heq := (Prod.mk.injEq _ _ _ _).mp h
    obtain ⟨rfl, rfl⟩ := hpn.syntheticN_injective heq.1
    rw [heq.2]
    -- Now need: oneV = if ∃ u ∈ vs, (n, u) ∈ S_Ψ then zeroV else oneV.
    -- Since hsat : S_Ψ ⊨ ¬(.dep n vs), the existential is false, so RHS = oneV.
    have : ¬ ∃ u ∈ vs, ((n, u) : Package N V) ∈ S_Ψ := hsat
    simp [this]
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetTaken_neg_conj] at h
    apply witnessSetTaken_negDep_det S_Ψ (.disj (.neg ψ_L) (.neg ψ_R)) _ n vs v h
    simp only [Formula.satisfies] at hsat
    exact (not_and_or.mp hsat)
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetTaken_neg_disj] at h
    apply witnessSetTaken_negDep_det S_Ψ (.conj (.neg ψ_L) (.neg ψ_R)) _ n vs v h
    simp only [Formula.satisfies] at hsat
    exact (not_or.mp hsat)
  | .neg (.neg ψ') =>
    rw [witnessSetTaken_neg_neg] at h
    apply witnessSetTaken_negDep_det S_Ψ ψ' _ n vs v h
    simp only [Formula.satisfies] at hsat
    exact not_not.mp hsat
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

/-- Every witness in `witnessSetUntaken` is a syntheticN or disjunctN
(in fact only syntheticN). -/
lemma witnessSetUntaken_name_classify [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V) (n : N') (v : V')
    (h : (n, v) ∈ witnessSetUntaken S_Ψ ψ) :
    (∃ n' vs, n = hpn.syntheticN n' vs) ∨ (∃ ψ_L ψ_R, n = hpn.disjunctN ψ_L ψ_R) := by
  match ψ with
  | .dep _ _ => simp at h
  | .conj ψ_L ψ_R =>
    simp only [witnessSetUntaken_conj, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_name_classify S_Ψ ψ_L n v)
      (witnessSetUntaken_name_classify S_Ψ ψ_R n v)
  | .disj ψ_L ψ_R =>
    simp only [witnessSetUntaken_disj, Finset.mem_union] at h
    exact h.elim
      (witnessSetUntaken_name_classify S_Ψ ψ_L n v)
      (witnessSetUntaken_name_classify S_Ψ ψ_R n v)
  | .neg (.dep n' vs) =>
    simp only [witnessSetUntaken_neg_dep] at h
    split at h
    · simp only [Finset.mem_singleton] at h
      have heq := (Prod.mk.injEq _ _ _ _).mp h
      exact Or.inl ⟨n', vs, heq.1⟩
    · simp at h
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetUntaken_neg_conj] at h
    exact witnessSetUntaken_name_classify S_Ψ (.disj (.neg ψ_L) (.neg ψ_R)) n v h
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetUntaken_neg_disj] at h
    exact witnessSetUntaken_name_classify S_Ψ (.conj (.neg ψ_L) (.neg ψ_R)) n v h
  | .neg (.neg ψ') =>
    rw [witnessSetUntaken_neg_neg] at h
    exact witnessSetUntaken_name_classify S_Ψ ψ' n v h
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

/-- Every witness in `witnessSetTaken` is either a syntheticN or a disjunctN. -/
lemma witnessSetTaken_name_classify [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V) (n : N') (v : V')
    (h : (n, v) ∈ witnessSetTaken S_Ψ ψ) :
    (∃ n' vs, n = hpn.syntheticN n' vs) ∨ (∃ ψ_L ψ_R, n = hpn.disjunctN ψ_L ψ_R) := by
  match ψ with
  | .dep _ _ => simp at h
  | .conj ψ_L ψ_R =>
    simp only [witnessSetTaken_conj, Finset.mem_union] at h
    exact h.elim
      (witnessSetTaken_name_classify S_Ψ ψ_L n v)
      (witnessSetTaken_name_classify S_Ψ ψ_R n v)
  | .disj ψ_L ψ_R =>
    simp only [witnessSetTaken_disj] at h
    split at h
    · simp only [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with (hsing | hL) | hU
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        exact Or.inr ⟨ψ_L, ψ_R, heq.1⟩
      · exact witnessSetTaken_name_classify S_Ψ ψ_L n v hL
      · exact witnessSetUntaken_name_classify S_Ψ ψ_R n v hU
    · simp only [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with (hsing | hU) | hR
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        exact Or.inr ⟨ψ_L, ψ_R, heq.1⟩
      · exact witnessSetUntaken_name_classify S_Ψ ψ_L n v hU
      · exact witnessSetTaken_name_classify S_Ψ ψ_R n v hR
  | .neg (.dep n' vs) =>
    simp only [witnessSetTaken_neg_dep, Finset.mem_singleton] at h
    have heq := (Prod.mk.injEq _ _ _ _).mp h
    exact Or.inl ⟨n', vs, heq.1⟩
  | .neg (.conj ψ_L ψ_R) =>
    rw [witnessSetTaken_neg_conj] at h
    exact witnessSetTaken_name_classify S_Ψ (.disj (.neg ψ_L) (.neg ψ_R)) n v h
  | .neg (.disj ψ_L ψ_R) =>
    rw [witnessSetTaken_neg_disj] at h
    exact witnessSetTaken_name_classify S_Ψ (.conj (.neg ψ_L) (.neg ψ_R)) n v h
  | .neg (.neg ψ') =>
    rw [witnessSetTaken_neg_neg] at h
    exact witnessSetTaken_name_classify S_Ψ ψ' n v h
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

/-- For any witness `(n, v)` in a context-appropriate witness set, the version
`v` is uniquely determined by `n` and `S_Ψ` (independent of which formula
generated the witness). -/
private lemma witnessSet_version_pinning [DecidableEq N] [DecidableEq V]
    {R_Ψ : Real N V} {Δ_Ψ : PFDepRel N V} {r : Package N V} {S_Ψ : Finset (Package N V)}
    (hres : IsPFResolution R_Ψ Δ_Ψ r S_Ψ)
    {n : N'} {v₁ v₂ : V'}
    (h1 : ∃ p ψ, (p, ψ) ∈ Δ_Ψ ∧
      (n, v₁) ∈ (if p ∈ S_Ψ then witnessSetTaken S_Ψ ψ else witnessSetUntaken S_Ψ ψ))
    (h2 : ∃ p ψ, (p, ψ) ∈ Δ_Ψ ∧
      (n, v₂) ∈ (if p ∈ S_Ψ then witnessSetTaken S_Ψ ψ else witnessSetUntaken S_Ψ ψ)) :
    v₁ = v₂ := by
  obtain ⟨p₁, ψ₁, hd₁, hw₁⟩ := h1
  obtain ⟨p₂, ψ₂, hd₂, hw₂⟩ := h2
  -- Use the discriminator `trySyntheticN` to test if `n` is a syntheticN.
  match hsyn : hpn.trySyntheticN n with
  | some (n', vs) =>
    -- n = syntheticN n' vs (by trySyntheticN_some).
    have hneq : n = hpn.syntheticN n' vs := (hpn.trySyntheticN_some _ _ hsyn).symm
    subst hneq
    -- Now compute v₁ and v₂ from each context.
    have getv : ∀ {p ψ v}, (p, ψ) ∈ Δ_Ψ →
        (hpn.syntheticN n' vs, v) ∈
          (if p ∈ S_Ψ then witnessSetTaken S_Ψ ψ else witnessSetUntaken S_Ψ ψ) →
        v = if ∃ u ∈ vs, ((n', u) : Package N V) ∈ S_Ψ then hpv.zeroV else hpv.oneV := by
      intro p ψ v hd hmem
      split at hmem
      · rename_i hpS
        have hsat : S_Ψ ⊨ ψ := hres.formula_closure p hpS ψ hd
        exact witnessSetTaken_negDep_det S_Ψ ψ hsat n' vs v hmem
      · have hv := witnessSetUntaken_negDep_det S_Ψ ψ n' vs v hmem
        have hex := witnessSetUntaken_negDep_exists S_Ψ ψ n' vs v hmem
        rw [hv, if_pos hex]
    rw [getv hd₁ hw₁, getv hd₂ hw₂]
  | none =>
    -- n is not a syntheticN. Use the classify lemma to identify n as a disjunctN.
    have hcls₁ : (∃ n' vs, n = hpn.syntheticN n' vs) ∨ (∃ ψ_L ψ_R, n = hpn.disjunctN ψ_L ψ_R) := by
      split at hw₁
      · exact witnessSetTaken_name_classify S_Ψ ψ₁ n v₁ hw₁
      · exact witnessSetUntaken_name_classify S_Ψ ψ₁ n v₁ hw₁
    rcases hcls₁ with ⟨n', vs, hn⟩ | ⟨ψ_L, ψ_R, hn⟩
    · -- contradicts hsyn
      subst hn
      simp [hpn.trySyntheticN_syntheticN] at hsyn
    · -- n = disjunctN ψ_L ψ_R.
      subst hn
      -- Both witnesses must be in witnessSetTaken (untaken can't produce disjunctN).
      have getv : ∀ {p ψ v}, (p, ψ) ∈ Δ_Ψ →
          (hpn.disjunctN ψ_L ψ_R, v) ∈
            (if p ∈ S_Ψ then witnessSetTaken S_Ψ ψ else witnessSetUntaken S_Ψ ψ) →
          v = if S_Ψ ⊨ ψ_L then hpv.zeroV else hpv.oneV := by
        intro p ψ v hd hmem
        split at hmem
        · exact witnessSetTaken_disjunct_det S_Ψ ψ ψ_L ψ_R v hmem
        · exact (witnessSetUntaken_disjunct_det S_Ψ ψ ψ_L ψ_R v hmem).elim
      rw [getv hd₁ hw₁, getv hd₂ hw₂]

/-! ## Dep-closure helpers

For each encoded edge `(q, m, vs)` with `q ∈ CW`, find a witness. -/

/-- Combined dep-closure lemma handling both taken and untaken contexts.

The `hwit` parameter is an OR:
- `Or.inr ⟨hsat, hwit_taken⟩`: taken context (S_Ψ ⊨ ψ, witnessSetTaken ⊆ CW)
- `Or.inl ⟨hq₀, hwit_untaken⟩`: untaken context (q₀ ∉ CW, witnessSetUntaken ⊆ CW)

In the disjunction case, body sub-formulas may switch context: a sub-formula's
wrapper may be in CW (from a taken formula elsewhere), requiring the taken
approach even within an overall untaken context. The `hCW_disj_zero` and
`hCW_disj_one` hypotheses provide the necessary satisfaction and witness-set
information for such cross-context switches. -/
private lemma encodeNNF_dep_closure [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V))
    (CW : Finset (Package N' V'))
    (mem_embed : ∀ p, p ∈ S_Ψ → embedPkg p ∈ CW)
    (hCW_orig : ∀ n v, (hpn.origN n, v) ∈ CW → ∃ p ∈ S_Ψ, embedPkg p = (hpn.origN n, v))
    (hCW_disj_zero : ∀ ψ_L ψ_R, (hpn.disjunctN ψ_L ψ_R, hpv.zeroV) ∈ CW →
        (S_Ψ ⊨ ψ_L) ∧ witnessSetTaken S_Ψ ψ_L ⊆ CW ∧ witnessSetUntaken S_Ψ ψ_R ⊆ CW)
    (hCW_disj_one : ∀ ψ_L ψ_R, (hpn.disjunctN ψ_L ψ_R, hpv.oneV) ∈ CW →
        (S_Ψ ⊨ ψ_R) ∧ witnessSetUntaken S_Ψ ψ_L ⊆ CW ∧ witnessSetTaken S_Ψ ψ_R ⊆ CW)
    (q₀ : Package N' V')
    (ψ : Formula N V)
    (hwit : (q₀ ∉ CW ∧ witnessSetUntaken S_Ψ ψ ⊆ CW) ∨
            ((S_Ψ ⊨ ψ) ∧ witnessSetTaken S_Ψ ψ ⊆ CW))
    (q : Package N' V')
    (m : N') (vs : Finset V')
    (henc : (q, m, vs) ∈ encodeNNF q₀ ψ)
    (hq : q ∈ CW) :
    ∃ v ∈ vs, (m, v) ∈ CW := by
  match ψ with
  | .dep n dvs =>
    simp only [encodeNNF, Finset.mem_singleton, Prod.mk.injEq] at henc
    obtain ⟨rfl, rfl, rfl⟩ := henc
    rcases hwit with ⟨hq₀, _⟩ | ⟨hsat, _⟩
    · exact absurd hq hq₀
    · obtain ⟨v, hv, hvS⟩ := hsat
      exact ⟨hpv.origV v, Finset.mem_map.mpr ⟨v, hv, rfl⟩, mem_embed _ hvS⟩
  | .conj ψ_L ψ_R =>
    simp only [encodeNNF, Finset.mem_union] at henc
    rcases henc with hL | hR
    · have hwit' : (q₀ ∉ CW ∧ witnessSetUntaken S_Ψ ψ_L ⊆ CW) ∨
          ((S_Ψ ⊨ ψ_L) ∧ witnessSetTaken S_Ψ ψ_L ⊆ CW) := by
        rcases hwit with ⟨hq₀, hu⟩ | ⟨hsat, ht⟩
        · exact Or.inl ⟨hq₀, fun x hx => hu (by simp [witnessSetUntaken_conj]; exact Or.inl hx)⟩
        · exact Or.inr ⟨hsat.1, fun x hx => ht (by simp [witnessSetTaken_conj]; exact Or.inl hx)⟩
      exact encodeNNF_dep_closure S_Ψ CW mem_embed hCW_orig hCW_disj_zero hCW_disj_one
        q₀ ψ_L hwit' q m vs hL hq
    · have hwit' : (q₀ ∉ CW ∧ witnessSetUntaken S_Ψ ψ_R ⊆ CW) ∨
          ((S_Ψ ⊨ ψ_R) ∧ witnessSetTaken S_Ψ ψ_R ⊆ CW) := by
        rcases hwit with ⟨hq₀, hu⟩ | ⟨hsat, ht⟩
        · exact Or.inl ⟨hq₀, fun x hx => hu (by simp [witnessSetUntaken_conj]; exact Or.inr hx)⟩
        · exact Or.inr ⟨hsat.2, fun x hx => ht (by simp [witnessSetTaken_conj]; exact Or.inr hx)⟩
      exact encodeNNF_dep_closure S_Ψ CW mem_embed hCW_orig hCW_disj_zero hCW_disj_one
        q₀ ψ_R hwit' q m vs hR hq
  | .disj ψ_L ψ_R =>
    rw [encodeNNF] at henc
    rw [Finset.mem_union, Finset.mem_union] at henc
    rcases henc with (hwrap | hbody) | hbody
    · -- wrapper edge: q = q₀
      simp only [Finset.mem_singleton, Prod.mk.injEq] at hwrap
      obtain ⟨rfl, rfl, rfl⟩ := hwrap
      rcases hwit with ⟨hq₀, _⟩ | ⟨hsat, hwit_t⟩
      · exact absurd hq hq₀
      · by_cases hψL_sat : S_Ψ ⊨ ψ_L
        · refine ⟨hpv.zeroV, Finset.mem_insert_self _ _, ?_⟩
          apply hwit_t; simp only [witnessSetTaken_disj, if_pos hψL_sat]
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
            (Finset.mem_singleton.mpr rfl))))
        · refine ⟨hpv.oneV, by simp [Finset.mem_insert], ?_⟩
          apply hwit_t; simp only [witnessSetTaken_disj, if_neg hψL_sat]
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
            (Finset.mem_singleton.mpr rfl))))
    · -- body ψ_L: new q₀' = (disjunctN ψ_L ψ_R, zeroV)
      by_cases hq₀' : (hpn.disjunctN ψ_L ψ_R, hpv.zeroV) ∈ CW
      · -- new q₀' ∈ CW: use taken via hCW_disj_zero
        obtain ⟨hsat_L, htL, _⟩ := hCW_disj_zero ψ_L ψ_R hq₀'
        exact encodeNNF_dep_closure S_Ψ CW mem_embed hCW_orig hCW_disj_zero hCW_disj_one
          _ ψ_L (Or.inr ⟨hsat_L, htL⟩) q m vs hbody hq
      · -- new q₀' ∉ CW: derive untaken witnesses
        have hwL : witnessSetUntaken S_Ψ ψ_L ⊆ CW := by
          rcases hwit with ⟨_, hu⟩ | ⟨_, ht⟩
          · exact fun x hx => hu (by simp [witnessSetUntaken_disj]; exact Or.inl hx)
          · by_cases hψL_sat : S_Ψ ⊨ ψ_L
            · -- sat ψ_L: (disjunctN, zeroV) ∈ witnessSetTaken (disj) ⊆ CW, contradiction
              exfalso; apply hq₀'
              apply ht; simp only [witnessSetTaken_disj, if_pos hψL_sat]
              exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
                (Finset.mem_singleton.mpr rfl))))
            · -- ¬sat ψ_L: witnessSetTaken (disj) = {oneV} ∪ untaken(ψ_L) ∪ taken(ψ_R)
              exact fun x hx => ht (by
                simp only [witnessSetTaken_disj, if_neg hψL_sat]
                exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hx))))
        exact encodeNNF_dep_closure S_Ψ CW mem_embed hCW_orig hCW_disj_zero hCW_disj_one
          _ ψ_L (Or.inl ⟨hq₀', hwL⟩) q m vs hbody hq
    · -- body ψ_R: new q₀' = (disjunctN ψ_L ψ_R, oneV)
      by_cases hq₀' : (hpn.disjunctN ψ_L ψ_R, hpv.oneV) ∈ CW
      · obtain ⟨hsat_R, _, htR⟩ := hCW_disj_one ψ_L ψ_R hq₀'
        exact encodeNNF_dep_closure S_Ψ CW mem_embed hCW_orig hCW_disj_zero hCW_disj_one
          _ ψ_R (Or.inr ⟨hsat_R, htR⟩) q m vs hbody hq
      · have hwR : witnessSetUntaken S_Ψ ψ_R ⊆ CW := by
          rcases hwit with ⟨_, hu⟩ | ⟨_, ht⟩
          · exact fun x hx => hu (by simp [witnessSetUntaken_disj]; exact Or.inr hx)
          · by_cases hψL_sat : S_Ψ ⊨ ψ_L
            · exact fun x hx => ht (by
                simp only [witnessSetTaken_disj, if_pos hψL_sat]
                exact Finset.mem_union.mpr (Or.inr hx))
            · exfalso; apply hq₀'
              apply ht; simp only [witnessSetTaken_disj, if_neg hψL_sat]
              exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
                (Finset.mem_singleton.mpr rfl))))
        exact encodeNNF_dep_closure S_Ψ CW mem_embed hCW_orig hCW_disj_zero hCW_disj_one
          _ ψ_R (Or.inl ⟨hq₀', hwR⟩) q m vs hbody hq
  | .neg (.dep n dvs) =>
    simp only [encodeNNF, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Prod.mk.injEq] at henc
    rcases henc with ⟨rfl, rfl, rfl⟩ | ⟨u, hu, rfl, rfl, rfl⟩
    · -- sentinel: q = q₀
      rcases hwit with ⟨hq₀, _⟩ | ⟨_, hwit_t⟩
      · exact absurd hq hq₀
      · refine ⟨hpv.oneV, Finset.mem_singleton.mpr rfl, ?_⟩
        apply hwit_t; simp only [witnessSetTaken_neg_dep]
        exact Finset.mem_singleton.mpr rfl
    · -- blocker: q = (origN n, origV u)
      obtain ⟨⟨pn, pv⟩, hpS, hpeq⟩ := hCW_orig n (hpv.origV u) hq
      simp only [embedPkg, Prod.mk.injEq] at hpeq
      have h1 := hpn.origN.injective hpeq.1
      have h2 := hpv.origV.injective hpeq.2
      subst h1; subst h2
      rcases hwit with ⟨_, hwit_u⟩ | ⟨hsat, _⟩
      · -- untaken: (n, u) ∈ S_Ψ, so witnessSetUntaken adds (syntheticN, zeroV)
        refine ⟨hpv.zeroV, Finset.mem_singleton.mpr rfl, ?_⟩
        apply hwit_u; simp only [witnessSetUntaken_neg_dep]
        rw [if_pos (⟨pv, hu, hpS⟩ : ∃ u ∈ dvs, ((pn, u) : Package N V) ∈ S_Ψ)]
        exact Finset.mem_singleton.mpr rfl
      · -- taken: S_Ψ ⊨ .neg(.dep n dvs) means no (n, u) ∈ S_Ψ. Contradiction.
        exfalso; exact hsat ⟨pv, hu, hpS⟩
  | .neg (.conj ψ_L ψ_R) =>
    have keyE : encodeNNF q₀ (.neg (.conj ψ_L ψ_R)) =
        encodeNNF q₀ (.disj (.neg ψ_L) (.neg ψ_R)) := by simp [encodeNNF]
    rw [keyE] at henc
    have hwit' : (q₀ ∉ CW ∧ witnessSetUntaken S_Ψ (.disj (.neg ψ_L) (.neg ψ_R)) ⊆ CW) ∨
        ((S_Ψ ⊨ Formula.disj (.neg ψ_L) (.neg ψ_R)) ∧
          witnessSetTaken S_Ψ (.disj (.neg ψ_L) (.neg ψ_R)) ⊆ CW) := by
      rcases hwit with ⟨hq₀, hu⟩ | ⟨hsat, ht⟩
      · exact Or.inl ⟨hq₀, by rw [← witnessSetUntaken_neg_conj]; exact hu⟩
      · exact Or.inr ⟨not_and_or.mp hsat, by rw [← witnessSetTaken_neg_conj]; exact ht⟩
    exact encodeNNF_dep_closure S_Ψ CW mem_embed hCW_orig hCW_disj_zero hCW_disj_one
      q₀ _ hwit' q m vs henc hq
  | .neg (.disj ψ_L ψ_R) =>
    have keyE : encodeNNF q₀ (.neg (.disj ψ_L ψ_R)) =
        encodeNNF q₀ (.conj (.neg ψ_L) (.neg ψ_R)) := by simp [encodeNNF]
    rw [keyE] at henc
    have hwit' : (q₀ ∉ CW ∧ witnessSetUntaken S_Ψ (.conj (.neg ψ_L) (.neg ψ_R)) ⊆ CW) ∨
        ((S_Ψ ⊨ Formula.conj (.neg ψ_L) (.neg ψ_R)) ∧
          witnessSetTaken S_Ψ (.conj (.neg ψ_L) (.neg ψ_R)) ⊆ CW) := by
      rcases hwit with ⟨hq₀, hu⟩ | ⟨hsat, ht⟩
      · exact Or.inl ⟨hq₀, by rw [← witnessSetUntaken_neg_disj]; exact hu⟩
      · exact Or.inr ⟨not_or.mp hsat, by rw [← witnessSetTaken_neg_disj]; exact ht⟩
    exact encodeNNF_dep_closure S_Ψ CW mem_embed hCW_orig hCW_disj_zero hCW_disj_one
      q₀ _ hwit' q m vs henc hq
  | .neg (.neg ψ') =>
    have keyE : encodeNNF q₀ (.neg (.neg ψ')) = encodeNNF q₀ ψ' := by simp [encodeNNF]
    rw [keyE] at henc
    have hwit' : (q₀ ∉ CW ∧ witnessSetUntaken S_Ψ ψ' ⊆ CW) ∨
        ((S_Ψ ⊨ ψ') ∧ witnessSetTaken S_Ψ ψ' ⊆ CW) := by
      rcases hwit with ⟨hq₀, hu⟩ | ⟨hsat, ht⟩
      · exact Or.inl ⟨hq₀, by rw [← witnessSetUntaken_neg_neg]; exact hu⟩
      · exact Or.inr ⟨not_not.mp hsat, by rw [← witnessSetTaken_neg_neg]; exact ht⟩
    exact encodeNNF_dep_closure S_Ψ CW mem_embed hCW_orig hCW_disj_zero hCW_disj_one
      q₀ ψ' hwit' q m vs henc hq
termination_by ψ.weight
decreasing_by all_goals (simp only [Formula.weight]; omega)

/-- Untaken-context dep-closure: when `q₀ ∉ CW` and `witnessSetUntaken S_Ψ ψ ⊆ CW`. -/
private lemma encodeNNF_dep_closure_untaken [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V))
    (CW : Finset (Package N' V'))
    (mem_embed : ∀ p, p ∈ S_Ψ → embedPkg p ∈ CW)
    (hCW_orig : ∀ n v, (hpn.origN n, v) ∈ CW → ∃ p ∈ S_Ψ, embedPkg p = (hpn.origN n, v))
    (hCW_disj_zero : ∀ ψ_L ψ_R, (hpn.disjunctN ψ_L ψ_R, hpv.zeroV) ∈ CW →
        (S_Ψ ⊨ ψ_L) ∧ witnessSetTaken S_Ψ ψ_L ⊆ CW ∧ witnessSetUntaken S_Ψ ψ_R ⊆ CW)
    (hCW_disj_one : ∀ ψ_L ψ_R, (hpn.disjunctN ψ_L ψ_R, hpv.oneV) ∈ CW →
        (S_Ψ ⊨ ψ_R) ∧ witnessSetUntaken S_Ψ ψ_L ⊆ CW ∧ witnessSetTaken S_Ψ ψ_R ⊆ CW)
    (q₀ : Package N' V')
    (hq₀ : q₀ ∉ CW)
    (ψ : Formula N V)
    (hwit : witnessSetUntaken S_Ψ ψ ⊆ CW)
    (q : Package N' V')
    (m : N') (vs : Finset V')
    (henc : (q, m, vs) ∈ encodeNNF q₀ ψ)
    (hq : q ∈ CW) :
    ∃ v ∈ vs, (m, v) ∈ CW :=
  encodeNNF_dep_closure S_Ψ CW mem_embed hCW_orig hCW_disj_zero hCW_disj_one
    q₀ ψ (Or.inl ⟨hq₀, hwit⟩) q m vs henc hq

/-- Taken-context dep-closure: when `S_Ψ ⊨ ψ` and `witnessSetTaken S_Ψ ψ ⊆ CW`. -/
private lemma encodeNNF_dep_closure_taken [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V))
    (CW : Finset (Package N' V'))
    (mem_embed : ∀ p, p ∈ S_Ψ → embedPkg p ∈ CW)
    (hCW_orig : ∀ n v, (hpn.origN n, v) ∈ CW → ∃ p ∈ S_Ψ, embedPkg p = (hpn.origN n, v))
    (hCW_disj_zero : ∀ ψ_L ψ_R, (hpn.disjunctN ψ_L ψ_R, hpv.zeroV) ∈ CW →
        (S_Ψ ⊨ ψ_L) ∧ witnessSetTaken S_Ψ ψ_L ⊆ CW ∧ witnessSetUntaken S_Ψ ψ_R ⊆ CW)
    (hCW_disj_one : ∀ ψ_L ψ_R, (hpn.disjunctN ψ_L ψ_R, hpv.oneV) ∈ CW →
        (S_Ψ ⊨ ψ_R) ∧ witnessSetUntaken S_Ψ ψ_L ⊆ CW ∧ witnessSetTaken S_Ψ ψ_R ⊆ CW)
    (q₀ : Package N' V')
    (ψ : Formula N V)
    (hsat : S_Ψ ⊨ ψ)
    (hwit : witnessSetTaken S_Ψ ψ ⊆ CW)
    (q : Package N' V')
    (m : N') (vs : Finset V')
    (henc : (q, m, vs) ∈ encodeNNF q₀ ψ)
    (hq : q ∈ CW) :
    ∃ v ∈ vs, (m, v) ∈ CW :=
  encodeNNF_dep_closure S_Ψ CW mem_embed hCW_orig hCW_disj_zero hCW_disj_one
    q₀ ψ (Or.inr ⟨hsat, hwit⟩) q m vs henc hq

/-! ## Monotonicity of witnessSetTaken for disjunct sub-formulas -/

private lemma witnessSetTaken_disj_zero_mono [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V)
    (ψ_L ψ_R : Formula N V)
    (hw : (hpn.disjunctN ψ_L ψ_R, hpv.zeroV) ∈ witnessSetTaken S_Ψ ψ) :
    (S_Ψ ⊨ ψ_L) ∧ witnessSetTaken S_Ψ ψ_L ⊆ witnessSetTaken S_Ψ ψ ∧
    witnessSetUntaken S_Ψ ψ_R ⊆ witnessSetTaken S_Ψ ψ := by
  match ψ with
  | .dep _ _ => exact absurd hw (by simp)
  | .conj ψ_a ψ_b =>
    simp only [witnessSetTaken_conj, Finset.mem_union] at hw
    rcases hw with hL | hR
    · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_zero_mono S_Ψ ψ_a ψ_L ψ_R hL
      exact ⟨hs, fun x hx => by simp only [witnessSetTaken_conj]; exact Finset.mem_union.mpr (Or.inl (h1 hx)),
             fun x hx => by simp only [witnessSetTaken_conj]; exact Finset.mem_union.mpr (Or.inl (h2 hx))⟩
    · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_zero_mono S_Ψ ψ_b ψ_L ψ_R hR
      exact ⟨hs, fun x hx => by simp only [witnessSetTaken_conj]; exact Finset.mem_union.mpr (Or.inr (h1 hx)),
             fun x hx => by simp only [witnessSetTaken_conj]; exact Finset.mem_union.mpr (Or.inr (h2 hx))⟩
  | .disj ψ_a ψ_b =>
    simp only [witnessSetTaken_disj] at hw
    split at hw
    · rename_i hψa_sat
      simp only [Finset.mem_union, Finset.mem_singleton] at hw
      rcases hw with (hsing | hL) | hU
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        obtain ⟨rfl, rfl⟩ := hpn.disjunctN_injective heq.1
        refine ⟨hψa_sat, ?_, ?_⟩
        · intro x hx; simp only [witnessSetTaken_disj, if_pos hψa_sat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inl (Or.inr hx)
        · intro x hx; simp only [witnessSetTaken_disj, if_pos hψa_sat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inr hx
      · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_zero_mono S_Ψ ψ_a ψ_L ψ_R hL
        refine ⟨hs, ?_, ?_⟩ <;> {
          intro x hx; simp only [witnessSetTaken_disj, if_pos hψa_sat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inl (Or.inr (by first | exact h1 hx | exact h2 hx)) }
      · exact absurd hU (witnessSetUntaken_disjunct_det S_Ψ ψ_b ψ_L ψ_R _)
    · rename_i hψa_unsat
      simp only [Finset.mem_union, Finset.mem_singleton] at hw
      rcases hw with (hsing | hU) | hR
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        exact absurd heq.2 hpv.zeroV_ne_oneV
      · exact absurd hU (witnessSetUntaken_disjunct_det S_Ψ ψ_a ψ_L ψ_R _)
      · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_zero_mono S_Ψ ψ_b ψ_L ψ_R hR
        refine ⟨hs, ?_, ?_⟩ <;> {
          intro x hx; simp only [witnessSetTaken_disj, if_neg hψa_unsat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inr (by first | exact h1 hx | exact h2 hx) }
  | .neg (.dep n vs) =>
    simp only [witnessSetTaken_neg_dep, Finset.mem_singleton, Prod.mk.injEq] at hw
    exact absurd hw.1 (hpn.disjunctN_ne_syntheticN ψ_L ψ_R n vs)
  | .neg (.conj ψ_a ψ_b) =>
    rw [witnessSetTaken_neg_conj] at hw ⊢
    exact witnessSetTaken_disj_zero_mono S_Ψ (.disj (.neg ψ_a) (.neg ψ_b)) ψ_L ψ_R hw
  | .neg (.disj ψ_a ψ_b) =>
    rw [witnessSetTaken_neg_disj] at hw ⊢
    exact witnessSetTaken_disj_zero_mono S_Ψ (.conj (.neg ψ_a) (.neg ψ_b)) ψ_L ψ_R hw
  | .neg (.neg ψ') =>
    rw [witnessSetTaken_neg_neg] at hw ⊢
    exact witnessSetTaken_disj_zero_mono S_Ψ ψ' ψ_L ψ_R hw
termination_by ψ.weight
decreasing_by all_goals (simp only [Formula.weight]; omega)

private lemma witnessSetTaken_disj_one_mono [DecidableEq N] [DecidableEq V]
    (S_Ψ : Finset (Package N V))
    (ψ : Formula N V)
    (hsat : S_Ψ ⊨ ψ)
    (ψ_L ψ_R : Formula N V)
    (hw : (hpn.disjunctN ψ_L ψ_R, hpv.oneV) ∈ witnessSetTaken S_Ψ ψ) :
    (S_Ψ ⊨ ψ_R) ∧ witnessSetUntaken S_Ψ ψ_L ⊆ witnessSetTaken S_Ψ ψ ∧
    witnessSetTaken S_Ψ ψ_R ⊆ witnessSetTaken S_Ψ ψ := by
  match ψ with
  | .dep _ _ => exact absurd hw (by simp)
  | .conj ψ_a ψ_b =>
    simp only [witnessSetTaken_conj, Finset.mem_union] at hw
    rcases hw with hL | hR
    · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_one_mono S_Ψ ψ_a hsat.1 ψ_L ψ_R hL
      exact ⟨hs, fun x hx => by simp only [witnessSetTaken_conj]; exact Finset.mem_union.mpr (Or.inl (h1 hx)),
             fun x hx => by simp only [witnessSetTaken_conj]; exact Finset.mem_union.mpr (Or.inl (h2 hx))⟩
    · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_one_mono S_Ψ ψ_b hsat.2 ψ_L ψ_R hR
      exact ⟨hs, fun x hx => by simp only [witnessSetTaken_conj]; exact Finset.mem_union.mpr (Or.inr (h1 hx)),
             fun x hx => by simp only [witnessSetTaken_conj]; exact Finset.mem_union.mpr (Or.inr (h2 hx))⟩
  | .disj ψ_a ψ_b =>
    simp only [witnessSetTaken_disj] at hw
    split at hw
    · rename_i hψa_sat
      simp only [Finset.mem_union, Finset.mem_singleton] at hw
      rcases hw with (hsing | hL) | hU
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        exact absurd heq.2.symm hpv.zeroV_ne_oneV
      · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_one_mono S_Ψ ψ_a hψa_sat ψ_L ψ_R hL
        refine ⟨hs, ?_, ?_⟩ <;> {
          intro x hx; simp only [witnessSetTaken_disj, if_pos hψa_sat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inl (Or.inr (by first | exact h1 hx | exact h2 hx)) }
      · exact absurd hU (witnessSetUntaken_disjunct_det S_Ψ ψ_b ψ_L ψ_R _)
    · rename_i hψa_unsat
      simp only [Finset.mem_union, Finset.mem_singleton] at hw
      rcases hw with (hsing | hU) | hR
      · have heq := (Prod.mk.injEq _ _ _ _).mp hsing
        obtain ⟨rfl, rfl⟩ := hpn.disjunctN_injective heq.1
        refine ⟨hsat.resolve_left hψa_unsat, ?_, ?_⟩
        · intro x hx; simp only [witnessSetTaken_disj, if_neg hψa_unsat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inl (Or.inr hx)
        · intro x hx; simp only [witnessSetTaken_disj, if_neg hψa_unsat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inr hx
      · exact absurd hU (witnessSetUntaken_disjunct_det S_Ψ ψ_a ψ_L ψ_R _)
      · obtain ⟨hs, h1, h2⟩ := witnessSetTaken_disj_one_mono S_Ψ ψ_b (hsat.resolve_left hψa_unsat) ψ_L ψ_R hR
        refine ⟨hs, ?_, ?_⟩ <;> {
          intro x hx; simp only [witnessSetTaken_disj, if_neg hψa_unsat, Finset.mem_union, Finset.mem_singleton]
          exact Or.inr (by first | exact h1 hx | exact h2 hx) }
  | .neg (.dep n vs) =>
    simp only [witnessSetTaken_neg_dep, Finset.mem_singleton, Prod.mk.injEq] at hw
    exact absurd hw.1 (hpn.disjunctN_ne_syntheticN ψ_L ψ_R n vs)
  | .neg (.conj ψ_a ψ_b) =>
    rw [witnessSetTaken_neg_conj] at hw ⊢
    exact witnessSetTaken_disj_one_mono S_Ψ _ (by exact not_and_or.mp hsat) ψ_L ψ_R hw
  | .neg (.disj ψ_a ψ_b) =>
    rw [witnessSetTaken_neg_disj] at hw ⊢
    exact witnessSetTaken_disj_one_mono S_Ψ _ (by exact not_or.mp hsat) ψ_L ψ_R hw
  | .neg (.neg ψ') =>
    rw [witnessSetTaken_neg_neg] at hw ⊢
    exact witnessSetTaken_disj_one_mono S_Ψ ψ' (by exact not_not.mp hsat) ψ_L ψ_R hw
termination_by ψ.weight
decreasing_by all_goals (simp only [Formula.weight]; omega)

/-! ## CW disjunct structure lemmas -/

private lemma completenessWitness_disj_zero [DecidableEq N] [DecidableEq V]
    {S_Ψ : Finset (Package N V)} {Δ_Ψ : PFDepRel N V}
    (ψ_L ψ_R : Formula N V)
    (hmem : (hpn.disjunctN ψ_L ψ_R, hpv.zeroV) ∈ completenessWitness S_Ψ Δ_Ψ) :
    (S_Ψ ⊨ ψ_L) ∧ witnessSetTaken S_Ψ ψ_L ⊆ completenessWitness S_Ψ Δ_Ψ ∧
    witnessSetUntaken S_Ψ ψ_R ⊆ completenessWitness S_Ψ Δ_Ψ := by
  obtain ⟨⟨p, ψ⟩, hdep, hw⟩ : ∃ p ψ, (p, ψ) ∈ Δ_Ψ ∧ (hpn.disjunctN ψ_L ψ_R, hpv.zeroV) ∈ (if p ∈ S_Ψ then witnessSetTaken S_Ψ ψ else witnessSetUntaken S_Ψ ψ) := by
    unfold completenessWitness at hmem; simp_all +decide [ Finset.mem_union, Finset.mem_image ] ;
    rcases hmem with ( ⟨ a, b, hab, h ⟩ | ⟨ a, b, ψ, hdep, hmem ⟩ );
    · unfold embedPkg at h; simp_all +decide [ hpn.origN_ne_disjunctN ] ;
    · exact ⟨ a, b, ψ, hdep, hmem ⟩;
  split_ifs at hw <;> simp_all +decide [ completenessWitness ];
  · have := witnessSetTaken_disj_zero_mono S_Ψ hdep ψ_L ψ_R hw.2;
    exact ⟨ this.1, Finset.Subset.trans this.2.1 ( Finset.subset_iff.mpr fun x hx => Finset.mem_union_right _ ( Finset.mem_biUnion.mpr ⟨ _, hw.1, by aesop ⟩ ) ), Finset.Subset.trans this.2.2 ( Finset.subset_iff.mpr fun x hx => Finset.mem_union_right _ ( Finset.mem_biUnion.mpr ⟨ _, hw.1, by aesop ⟩ ) ) ⟩;
  · exact False.elim ( witnessSetUntaken_disjunct_det S_Ψ hdep ψ_L ψ_R _ hw.2 )

private lemma completenessWitness_disj_one [DecidableEq N] [DecidableEq V]
    {R_Ψ : Real N V} {S_Ψ : Finset (Package N V)} {Δ_Ψ : PFDepRel N V}
    {r : Package N V}
    (hres : IsPFResolution R_Ψ Δ_Ψ r S_Ψ)
    (ψ_L ψ_R : Formula N V)
    (hmem : (hpn.disjunctN ψ_L ψ_R, hpv.oneV) ∈ completenessWitness S_Ψ Δ_Ψ) :
    (S_Ψ ⊨ ψ_R) ∧ witnessSetUntaken S_Ψ ψ_L ⊆ completenessWitness S_Ψ Δ_Ψ ∧
    witnessSetTaken S_Ψ ψ_R ⊆ completenessWitness S_Ψ Δ_Ψ := by
  unfold completenessWitness at hmem;
  simp +zetaDelta at *;
  rcases hmem with ( ⟨ a, b, hab, h ⟩ | ⟨ a, b, c, h₁, h₂ ⟩ );
  · unfold embedPkg at h; simp_all +decide ;
  · split_ifs at h₂;
    · have := witnessSetTaken_disj_one_mono S_Ψ c ( hres.formula_closure ( a, b ) ‹_› c h₁ ) ψ_L ψ_R h₂;
      refine' ⟨ this.1, Finset.Subset.trans this.2.1 _, Finset.Subset.trans this.2.2 _ ⟩;
      · unfold completenessWitness;
        grind +revert;
      · unfold completenessWitness;
        grind;
    · exact False.elim ( witnessSetUntaken_disjunct_det S_Ψ c ψ_L ψ_R _ h₂ )

/-! ## `pkgFormula_completeness`

The proof structure:
- `subset`: each witness package is in `pfReal` (via `witnessSet*_subset_witnessPackages`).
- `root_mem`: trivial from `S_Ψ.image embedPkg`.
- `version_unique`: combine the determinism lemmas across taken and untaken
  contexts using the satisfaction-aware `witnessSetTaken_negDep_det`.
- `dep_closure`: the structurally hard case, proved by a helper inducting on
  the formula.  See `encodeNNF_dep_closure` below. -/

-- Paper Thm 4.5.6 (Package Formula Reduction Completeness).
theorem pkgFormula_completeness [DecidableEq N] [DecidableEq V]
    (R_Ψ : Real N V) (Δ_Ψ : PFDepRel N V)
    (r : Package N V)
    (S_Ψ : Finset (Package N V))
    (hres : IsPFResolution R_Ψ Δ_Ψ r S_Ψ) :
    IsResolution (pfReal R_Ψ Δ_Ψ) (pfDeps Δ_Ψ) (embedPkg r)
      (completenessWitness S_Ψ Δ_Ψ) := by
  -- Convenience facts
  have mem_embed : ∀ p, p ∈ S_Ψ → embedPkg p ∈ completenessWitness S_Ψ Δ_Ψ := by
    intro p hp
    simp only [completenessWitness, Finset.mem_union, Finset.mem_image]
    exact Or.inl ⟨p, hp, rfl⟩
  have hCW_orig : ∀ n v, (hpn.origN n, v) ∈ completenessWitness S_Ψ Δ_Ψ →
      ∃ p ∈ S_Ψ, embedPkg p = (hpn.origN n, v) := by
    intro n v hv
    simp only [completenessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hv
    rcases hv with ⟨p, hp, hpe⟩ | ⟨⟨p, ψ⟩, _, hw⟩
    · exact ⟨p, hp, hpe⟩
    · split at hw
      · exact absurd hw (witnessSetTaken_not_orig S_Ψ ψ n _)
      · exact absurd hw (witnessSetUntaken_not_orig S_Ψ ψ n _)
  -- CW disjunct hypotheses
  have hCW_disj_zero : ∀ ψ_L ψ_R, (hpn.disjunctN ψ_L ψ_R, hpv.zeroV) ∈
      completenessWitness S_Ψ Δ_Ψ →
      (S_Ψ ⊨ ψ_L) ∧ witnessSetTaken S_Ψ ψ_L ⊆ completenessWitness S_Ψ Δ_Ψ ∧
      witnessSetUntaken S_Ψ ψ_R ⊆ completenessWitness S_Ψ Δ_Ψ :=
    fun ψ_L ψ_R h => completenessWitness_disj_zero ψ_L ψ_R h
  have hCW_disj_one : ∀ ψ_L ψ_R, (hpn.disjunctN ψ_L ψ_R, hpv.oneV) ∈
      completenessWitness S_Ψ Δ_Ψ →
      (S_Ψ ⊨ ψ_R) ∧ witnessSetUntaken S_Ψ ψ_L ⊆ completenessWitness S_Ψ Δ_Ψ ∧
      witnessSetTaken S_Ψ ψ_R ⊆ completenessWitness S_Ψ Δ_Ψ :=
    fun ψ_L ψ_R h => completenessWitness_disj_one hres ψ_L ψ_R h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- subset
    intro q hq
    simp only [completenessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hq
    rcases hq with ⟨p, hp, rfl⟩ | ⟨⟨p, ψ⟩, hdep, hw⟩
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨p, hres.subset hp, rfl⟩))
    · simp only [pfReal, Finset.mem_union, Finset.mem_biUnion]
      refine Or.inr ⟨⟨p, ψ⟩, hdep, ?_⟩
      split at hw
      · exact witnessSetTaken_subset_witnessPackages S_Ψ (embedPkg p) ψ hw
      · exact witnessSetUntaken_subset_witnessPackages S_Ψ (embedPkg p) ψ hw
  · -- root_mem
    exact mem_embed r hres.root_mem
  · -- dep_closure
    intro q hq m vs' hd
    simp only [pfDeps, Finset.mem_biUnion] at hd
    obtain ⟨⟨p, ψ⟩, hdep, henc⟩ := hd
    by_cases hp : p ∈ S_Ψ
    · -- taken case: have S_Ψ ⊨ ψ, witnessSetTaken ψ ⊆ CW.
      have hsat : S_Ψ ⊨ ψ := hres.formula_closure p hp ψ hdep
      have hwit : witnessSetTaken S_Ψ ψ ⊆ completenessWitness S_Ψ Δ_Ψ := by
        intro x hx
        simp only [completenessWitness, Finset.mem_union, Finset.mem_biUnion]
        refine Or.inr ⟨⟨p, ψ⟩, hdep, ?_⟩
        rw [if_pos hp]; exact hx
      exact encodeNNF_dep_closure_taken S_Ψ _ mem_embed hCW_orig
        hCW_disj_zero hCW_disj_one (embedPkg p) ψ hsat hwit
        q m vs' henc hq
    · -- untaken case: just witnessSetUntaken ψ ⊆ CW.
      have hwit : witnessSetUntaken S_Ψ ψ ⊆ completenessWitness S_Ψ Δ_Ψ := by
        intro x hx
        simp only [completenessWitness, Finset.mem_union, Finset.mem_biUnion]
        refine Or.inr ⟨⟨p, ψ⟩, hdep, ?_⟩
        rw [if_neg hp]; exact hx
      have hq₀ : embedPkg p ∉ completenessWitness S_Ψ Δ_Ψ := by
        intro hmem
        apply hp
        have : (hpn.origN p.1, hpv.origV p.2) ∈ completenessWitness S_Ψ Δ_Ψ := by
          show embedPkg p ∈ _; exact hmem
        obtain ⟨p', hp', hpe⟩ := hCW_orig p.1 (hpv.origV p.2) this
        simp only [embedPkg, Prod.mk.injEq] at hpe
        have h1 := hpn.origN.injective hpe.1
        have h2 := hpv.origV.injective hpe.2
        cases p with | mk n v => cases p' with | mk n' v' =>
        simp at h1 h2; subst h1; subst h2; exact hp'
      exact encodeNNF_dep_closure_untaken S_Ψ _ mem_embed hCW_orig
        hCW_disj_zero hCW_disj_one (embedPkg p) hq₀ ψ hwit
        q m vs' henc hq
  · -- version_unique
    intro n v₁ v₂ hv₁ hv₂
    simp only [completenessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
      at hv₁ hv₂
    rcases hv₁ with ⟨p₁, hp₁, heq1⟩ | ⟨⟨p₁, ψ₁⟩, hd₁, hw₁⟩ <;>
    rcases hv₂ with ⟨p₂, hp₂, heq2⟩ | ⟨⟨p₂, ψ₂⟩, hd₂, hw₂⟩
    · obtain ⟨n₁, w₁⟩ := p₁; obtain ⟨n₂, w₂⟩ := p₂
      simp only [embedPkg, Prod.mk.injEq] at heq1 heq2
      obtain ⟨h1n, rfl⟩ := heq1; obtain ⟨h2n, rfl⟩ := heq2
      have := hpn.origN.injective (h1n.trans h2n.symm); subst this
      exact congrArg hpv.origV (hres.version_unique _ _ _ hp₁ hp₂)
    · simp only [embedPkg, Prod.mk.injEq] at heq1
      obtain ⟨rfl, rfl⟩ := heq1
      split at hw₂
      · exact absurd hw₂ (witnessSetTaken_not_orig S_Ψ ψ₂ _ _)
      · exact absurd hw₂ (witnessSetUntaken_not_orig S_Ψ ψ₂ _ _)
    · simp only [embedPkg, Prod.mk.injEq] at heq2
      obtain ⟨rfl, rfl⟩ := heq2
      split at hw₁
      · exact absurd hw₁ (witnessSetTaken_not_orig S_Ψ ψ₁ _ _)
      · exact absurd hw₁ (witnessSetUntaken_not_orig S_Ψ ψ₁ _ _)
    · -- Both witnesses.  See `witnessSet_version_pinning` below.
      exact witnessSet_version_pinning hres ⟨p₁, ψ₁, hd₁, hw₁⟩ ⟨p₂, ψ₂, hd₂, hw₂⟩

end PackageCalculus.PkgFormula