import PackageCalculus.Versions.Formula
import PackageCalculus.Versions.Reduction.Definition
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Basic

set_option linter.unusedSectionVars false

namespace PackageCalculus

variable {V : Type*} [DecidableEq V]

/-! ## finsetToFormula: construct a VersionFormula from a target Finset -/

/-- Build a formula that is the disjunction of a non-empty list of formulas. -/
private def disjoinFormulas : List (VersionFormula V) → VersionFormula V
  | [] => .top  -- unreachable in practice
  | [φ] => φ
  | φ :: φs => .disj φ (disjoinFormulas φs)

/-- Build a formula for a contiguous range [lo, hi] (using ≥ lo ∧ ≤ hi),
    or just = v for a singleton. -/
private def rangeFormula [LinearOrder V] (lo hi : V) : VersionFormula V :=
  if lo = hi then .cmp .eq lo
  else .conj (.cmp .ge lo) (.cmp .le hi)

/-- Extend a range: consume consecutive repo versions that are in the target set.
    Returns the high end of the range and the remaining repo list. -/
private def extendRange [LinearOrder V] :
    List V → Finset V → V → V × List V
  | [], _, cur => (cur, [])
  | v :: vs, target, cur =>
    if v ∈ target then extendRange vs target v
    else (cur, v :: vs)

private theorem extendRange_length_le [LinearOrder V]
    (l : List V) (target : Finset V) (cur : V) :
    (extendRange l target cur).2.length ≤ l.length := by
  induction l generalizing cur with
  | nil => simp [extendRange]
  | cons v vs ih =>
    simp only [extendRange]; split
    · exact Nat.le_succ_of_le (ih v)
    · exact Nat.le_refl _

/-- Given a sorted repo list and target set, identify contiguous ranges
    in the target and build range formulas. -/
private def buildRanges [LinearOrder V] :
    List V → Finset V → List (VersionFormula V)
  | [], _ => []
  | v :: vs, target =>
    if v ∈ target then
      let result := extendRange vs target v
      rangeFormula v result.1 :: buildRanges result.2 target
    else
      buildRanges vs target
termination_by l => l.length
decreasing_by
  all_goals simp_wf
  all_goals (first | omega | (have := extendRange_length_le vs target v; omega))

/-- Convert a non-empty `Finset V` into a `VersionFormula V` that evaluates to
    exactly that set against the repository, via contiguous-range detection on the
    sorted repository. -/
def finsetToFormula [LinearOrder V]
    (repo : Finset V) (target : Finset V) (h : target.Nonempty) : VersionFormula V :=
  let sorted := repo.sort (· ≤ ·)
  let ranges := buildRanges sorted target
  match ranges with
  | [] =>
    -- fallback: pick an element from target
    .cmp .eq (target.min' h)
  | [φ] => φ
  | φ :: φs => disjoinFormulas (φ :: φs)

/-! ## Helper lemmas for finsetToFormula correctness -/

/-! We define a Set-based evaluation locally for proof purposes. The public
    theorem `finsetToFormula_eval` is stated in terms of the (Finset-based)
    `VersionFormula.eval`. -/

/-- Set-based comparison operator evaluation (proof-internal). -/
private def CmpOp.evalProp [LT V] (ω : CmpOp) (v c : V) : Prop :=
  match ω with
  | .ge => ¬(v < c)    -- v ≥ c
  | .gt => c < v
  | .le => ¬(c < v)    -- v ≤ c
  | .lt => v < c
  | .eq => v = c
  | .ne => v ≠ c

/-- Set-based formula evaluation (proof-internal). -/
private def VersionFormula.evalSet [LT V]
    (φ : VersionFormula V) (Vn : Set V) : Set V :=
  match φ with
  | .top => Vn
  | .conj φ₁ φ₂ => φ₁.evalSet Vn ∩ φ₂.evalSet Vn
  | .disj φ₁ φ₂ => φ₁.evalSet Vn ∪ φ₂.evalSet Vn
  | .cmp ω c => { v ∈ Vn | ω.evalProp v c }

/-- The Finset eval agrees with the Set eval when cast to Set. -/
private theorem eval_coe [LT V] [DecidableRel (· < · : V → V → Prop)]
    (φ : VersionFormula V) (Vn : Finset V) :
    ↑(φ.eval Vn) = φ.evalSet ↑Vn := by
  induction φ with
  | top => simp [VersionFormula.eval, VersionFormula.evalSet]
  | conj φ₁ φ₂ ih₁ ih₂ =>
    simp only [VersionFormula.eval, VersionFormula.evalSet, Finset.coe_inter]
    rw [ih₁, ih₂]
  | disj φ₁ φ₂ ih₁ ih₂ =>
    simp only [VersionFormula.eval, VersionFormula.evalSet, Finset.coe_union]
    rw [ih₁, ih₂]
  | cmp ω c =>
    ext v
    simp only [VersionFormula.eval, VersionFormula.evalSet, Finset.coe_filter,
      Set.mem_setOf_eq, Finset.mem_coe]
    constructor
    · rintro ⟨hv, hb⟩
      refine ⟨hv, ?_⟩
      cases ω <;> simp [CmpOp.eval, CmpOp.evalProp, decide_eq_true_eq] at hb ⊢ <;> exact hb
    · rintro ⟨hv, hp⟩
      refine ⟨hv, ?_⟩
      cases ω <;> simp [CmpOp.eval, CmpOp.evalProp, decide_eq_true_eq] at hp ⊢ <;> exact hp

/-- Every version formula evaluates to a subset of the input set. -/
private theorem evalSet_subset [LT V] (φ : VersionFormula V) (Vn : Set V) :
    φ.evalSet Vn ⊆ Vn := by
  induction φ with
  | top => exact Set.Subset.refl _
  | conj _ _ ih₁ _ => exact Set.inter_subset_left.trans ih₁
  | disj _ _ ih₁ ih₂ => exact Set.union_subset ih₁ ih₂
  | cmp _ _ => intro v hv; exact (Set.mem_sep_iff.mp hv).1

private theorem mem_rangeFormula_evalSet [LinearOrder V] (lo hi : V) (Vn : Set V) (hle : lo ≤ hi)
    (v : V) : v ∈ (rangeFormula lo hi).evalSet Vn ↔ v ∈ Vn ∧ lo ≤ v ∧ v ≤ hi := by
  by_cases heq : lo = hi
  · subst heq; unfold rangeFormula; simp only [ite_true]
    simp only [VersionFormula.evalSet, CmpOp.evalProp, Set.mem_sep_iff]
    exact ⟨fun ⟨hv, rfl⟩ => ⟨hv, le_refl _, le_refl _⟩,
           fun ⟨hv, hge, hle'⟩ => ⟨hv, le_antisymm hle' hge⟩⟩
  · simp only [rangeFormula, if_neg heq, VersionFormula.evalSet, CmpOp.evalProp,
      Set.mem_inter_iff, Set.mem_sep_iff]
    exact ⟨fun ⟨⟨hv1, hge⟩, ⟨_, hle'⟩⟩ => ⟨hv1, not_lt.mp hge, not_lt.mp hle'⟩,
           fun ⟨hv, hge, hle'⟩ => ⟨⟨hv, not_lt.mpr hge⟩, ⟨hv, not_lt.mpr hle'⟩⟩⟩

private theorem disjoinFormulas_mem [LT V] (Vn : Set V) (v : V) :
    ∀ (φ : VersionFormula V) (φs : List (VersionFormula V)),
      v ∈ (disjoinFormulas (φ :: φs)).evalSet Vn ↔ ∃ ψ, ψ ∈ (φ :: φs) ∧ v ∈ ψ.evalSet Vn
  | φ, [] => by
    simp only [disjoinFormulas, List.mem_singleton]
    exact ⟨fun h => ⟨φ, rfl, h⟩, fun ⟨ψ, hψ, hv⟩ => hψ ▸ hv⟩
  | φ, ψ :: ψs => by
    simp only [disjoinFormulas, VersionFormula.evalSet, Set.mem_union]
    rw [disjoinFormulas_mem Vn v ψ ψs]
    constructor
    · rintro (h | ⟨ψ', hψ', hv⟩)
      · exact ⟨φ, List.mem_cons_self, h⟩
      · exact ⟨ψ', List.mem_cons_of_mem φ hψ', hv⟩
    · rintro ⟨ψ', hψ', hv⟩
      rcases List.mem_cons.mp hψ' with rfl | hψ'
      · left; exact hv
      · right; exact ⟨ψ', hψ', hv⟩

/-! ### extendRange properties -/

private theorem extendRange_fst_eq_or_mem [LinearOrder V]
    (l : List V) (target : Finset V) (cur : V) :
    (extendRange l target cur).1 = cur ∨ (extendRange l target cur).1 ∈ l := by
  induction l generalizing cur with
  | nil => left; simp [extendRange]
  | cons w ws ih =>
    simp only [extendRange]; split
    · cases ih w with
      | inl h => right; rw [h]; exact List.mem_cons_self
      | inr h => right; exact List.mem_cons_of_mem w h
    · left; trivial

private theorem extendRange_fst_ge [LinearOrder V]
    (l : List V) (target : Finset V) (cur : V) (hge : ∀ x ∈ l, cur ≤ x) :
    cur ≤ (extendRange l target cur).1 := by
  cases extendRange_fst_eq_or_mem l target cur with
  | inl h => rw [h]
  | inr h => exact hge _ h

private theorem extendRange_snd_suffix [LinearOrder V]
    (l : List V) (target : Finset V) (cur : V) :
    (extendRange l target cur).2 <:+ l := by
  induction l generalizing cur with
  | nil => exact List.suffix_refl _
  | cons v vs ih =>
    simp only [extendRange]; split
    · exact List.IsSuffix.trans (ih v) (List.suffix_cons v vs)
    · exact List.suffix_refl _

private theorem extendRange_consumed_in_target [LinearOrder V]
    (l : List V) (target : Finset V) (cur : V) (v : V)
    (hv_in : v ∈ l) (hv_not_rest : v ∉ (extendRange l target cur).2) :
    v ∈ target := by
  induction l generalizing cur with
  | nil => exact absurd hv_in List.not_mem_nil
  | cons w ws ih =>
    simp only [extendRange] at hv_not_rest
    split at hv_not_rest
    case isTrue hmem =>
      rcases List.mem_cons.mp hv_in with rfl | hin
      · exact hmem
      · exact ih w hin hv_not_rest
    case isFalse =>
      rcases List.mem_cons.mp hv_in with rfl | hin
      · exact absurd List.mem_cons_self hv_not_rest
      · exact absurd (List.mem_cons_of_mem w hin) hv_not_rest

private theorem extendRange_not_target_in_rest [LinearOrder V]
    (l : List V) (target : Finset V) (cur : V) (v : V)
    (hv_in : v ∈ l) (hv_not_target : v ∉ target) :
    v ∈ (extendRange l target cur).2 := by
  induction l generalizing cur with
  | nil => exact absurd hv_in List.not_mem_nil
  | cons w ws ih =>
    simp only [extendRange]
    split
    case isTrue hmem =>
      rcases List.mem_cons.mp hv_in with rfl | hin
      · exact absurd hmem hv_not_target
      · exact ih w hin
    case isFalse => exact hv_in

private theorem extendRange_consumed_le_fst [LinearOrder V]
    (l : List V) (target : Finset V) (cur : V) (v : V)
    (hpw : l.Pairwise (· ≤ ·)) (hv_in : v ∈ l)
    (hv_not_rest : v ∉ (extendRange l target cur).2) :
    v ≤ (extendRange l target cur).1 := by
  induction l generalizing cur with
  | nil => exact absurd hv_in List.not_mem_nil
  | cons w ws ih =>
    have hpw' := (List.pairwise_cons.mp hpw).2
    have hwall := (List.pairwise_cons.mp hpw).1
    by_cases hmem : w ∈ target
    · -- w ∈ target: extendRange unfolds to recursive call
      simp only [extendRange, if_pos hmem] at hv_not_rest ⊢
      rcases List.mem_cons.mp hv_in with rfl | hin
      · exact extendRange_fst_ge ws target _ hwall
      · exact ih _ hpw' hin hv_not_rest
    · -- w ∉ target: remainder is w :: ws
      simp only [extendRange, if_neg hmem] at hv_not_rest
      exfalso
      rcases List.mem_cons.mp hv_in with rfl | hin
      · exact hv_not_rest List.mem_cons_self
      · exact hv_not_rest (List.mem_cons_of_mem w hin)

private theorem extendRange_rest_gt_fst [LinearOrder V]
    (l : List V) (target : Finset V) (cur : V)
    (hpw : l.Pairwise (· < ·)) (hgt_cur : ∀ x ∈ l, cur < x)
    (v : V) (hv : v ∈ (extendRange l target cur).2) :
    (extendRange l target cur).1 < v := by
  induction l generalizing cur with
  | nil => exact absurd hv List.not_mem_nil
  | cons w ws ih =>
    have hpw' := (List.pairwise_cons.mp hpw).2
    have hwall := (List.pairwise_cons.mp hpw).1
    simp only [extendRange] at hv
    split at hv
    case isTrue hmem =>
      simp only [extendRange, if_pos hmem]
      exact ih w hpw' (fun x hx => hwall x hx) hv
    case isFalse hmem =>
      simp only [extendRange, if_neg hmem]
      rcases List.mem_cons.mp hv with rfl | hin
      · exact hgt_cur v List.mem_cons_self
      · exact hgt_cur v (List.mem_cons_of_mem w hin)

/-! ### buildRanges correctness (using n-indexed induction) -/

private theorem buildRanges_evalSet_lo [LinearOrder V]
    (n : Nat) (l : List V) (hl : l.length ≤ n)
    (target : Finset V) (Vn : Set V) (hpw : l.Pairwise (· ≤ ·))
    (v : V) (φ : VersionFormula V) (hφ : φ ∈ buildRanges l target) (hv : v ∈ φ.evalSet Vn) :
    ∃ x ∈ l, x ≤ v := by
  induction n generalizing l v φ with
  | zero =>
    have := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hl)
    subst this; simp [buildRanges] at hφ
  | succ n ih =>
    cases l with
    | nil => simp [buildRanges] at hφ
    | cons w ws =>
      have hpw' := (List.pairwise_cons.mp hpw).2
      have hwall := (List.pairwise_cons.mp hpw).1
      have hlen_ws : ws.length ≤ n := by simp [List.length_cons] at hl; omega
      simp only [buildRanges] at hφ
      split at hφ
      case isTrue hmem =>
        set er := extendRange ws target w
        have hle_er : w ≤ er.1 := extendRange_fst_ge ws target w hwall
        have hlen_er : er.2.length ≤ n := by
          have h1 : er.2.length ≤ ws.length := extendRange_length_le ws target w
          omega
        rcases List.mem_cons.mp hφ with rfl | hφ_rest
        · exact ⟨w, List.mem_cons_self,
            ((mem_rangeFormula_evalSet w er.1 Vn hle_er v).mp hv).2.1⟩
        · obtain ⟨x, hx, hle'⟩ := ih er.2 hlen_er
            (List.Pairwise.sublist (extendRange_snd_suffix ws target w).sublist hpw')
            v φ hφ_rest hv
          exact ⟨x, List.mem_cons_of_mem w
            ((extendRange_snd_suffix ws target w).subset hx), hle'⟩
      case isFalse =>
        obtain ⟨x, hx, hle'⟩ := ih ws hlen_ws hpw' v φ hφ hv
        exact ⟨x, List.mem_cons_of_mem w hx, hle'⟩

private theorem buildRanges_sound [LinearOrder V]
    (n : Nat) (l : List V) (hl : l.length ≤ n)
    (target : Finset V) (Vn : Set V) (hpw_lt : l.Pairwise (· < ·))
    (v : V) (hv_in_l : v ∈ l)
    (φ : VersionFormula V) (hφ : φ ∈ buildRanges l target) (hv_φ : v ∈ φ.evalSet Vn) :
    v ∈ target := by
  induction n generalizing l v φ with
  | zero =>
    have := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hl)
    subst this; exact absurd hv_in_l List.not_mem_nil
  | succ n ih =>
    cases l with
    | nil => exact absurd hv_in_l List.not_mem_nil
    | cons w ws =>
      have hpw_lt' := (List.pairwise_cons.mp hpw_lt).2
      have hwall_lt := (List.pairwise_cons.mp hpw_lt).1
      have hpw_le' : ws.Pairwise (· ≤ ·) := hpw_lt'.imp (fun h => le_of_lt h)
      have hwall_le : ∀ x ∈ ws, w ≤ x := fun x hx => le_of_lt (hwall_lt x hx)
      have hlen_ws : ws.length ≤ n := by simp [List.length_cons] at hl; omega
      simp only [buildRanges] at hφ
      split at hφ
      case isTrue hmem_target =>
        set er := extendRange ws target w
        have hle_er : w ≤ er.1 := extendRange_fst_ge ws target w hwall_le
        have hlen_er : er.2.length ≤ n := by
          have h1 : er.2.length ≤ ws.length := extendRange_length_le ws target w; omega
        rcases List.mem_cons.mp hφ with rfl | hφ_rest
        · -- v ∈ rangeFormula w er.1
          rw [mem_rangeFormula_evalSet w er.1 Vn hle_er v] at hv_φ
          obtain ⟨_, hv_ge, hv_le⟩ := hv_φ
          rcases List.mem_cons.mp hv_in_l with rfl | hv_ws
          · exact hmem_target
          · by_contra hv_not_target
            have hv_rest := extendRange_not_target_in_rest ws target w v hv_ws hv_not_target
            exact absurd (lt_of_lt_of_le
              (extendRange_rest_gt_fst ws target w hpw_lt' hwall_lt v hv_rest) hv_le)
              (lt_irrefl _)
        · -- φ ∈ buildRanges er.2 target
          by_cases hv_rest : v ∈ er.2
          · exact ih er.2 hlen_er
              (List.Pairwise.sublist (extendRange_snd_suffix ws target w).sublist hpw_lt')
              v hv_rest φ hφ_rest hv_φ
          · rcases List.mem_cons.mp hv_in_l with rfl | hv_ws
            · exact hmem_target
            · exact extendRange_consumed_in_target ws target w v hv_ws hv_rest
      case isFalse hnotmem =>
        rcases List.mem_cons.mp hv_in_l with rfl | hv_ws
        · -- v = w ∉ target, but v ∈ some formula from buildRanges ws
          -- All formulas have lo from ws, and w < all ws elements
          have ⟨x, hx, hle⟩ := buildRanges_evalSet_lo n ws hlen_ws target Vn hpw_le'
            v φ hφ hv_φ
          exact absurd (lt_of_lt_of_le (hwall_lt x hx) hle) (lt_irrefl _)
        · exact ih ws hlen_ws hpw_lt' v hv_ws φ hφ hv_φ

private theorem buildRanges_complete [LinearOrder V]
    (n : Nat) (l : List V) (hl : l.length ≤ n)
    (target : Finset V) (Vn : Set V) (hpw_lt : l.Pairwise (· < ·))
    (v : V) (hv_in_l : v ∈ l) (hv_target : v ∈ target) (hv_Vn : v ∈ Vn) :
    ∃ φ, φ ∈ buildRanges l target ∧ v ∈ φ.evalSet Vn := by
  induction n generalizing l v with
  | zero =>
    have := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hl)
    subst this; exact absurd hv_in_l List.not_mem_nil
  | succ n ih =>
    cases l with
    | nil => exact absurd hv_in_l List.not_mem_nil
    | cons w ws =>
      have hpw_lt' := (List.pairwise_cons.mp hpw_lt).2
      have hwall_lt := (List.pairwise_cons.mp hpw_lt).1
      have hpw_le' : ws.Pairwise (· ≤ ·) := hpw_lt'.imp (fun h => le_of_lt h)
      have hwall_le : ∀ x ∈ ws, w ≤ x := fun x hx => le_of_lt (hwall_lt x hx)
      have hlen_ws : ws.length ≤ n := by simp [List.length_cons] at hl; omega
      simp only [buildRanges]
      split
      case isTrue hmem_target =>
        set er := extendRange ws target w
        have hle_er : w ≤ er.1 := extendRange_fst_ge ws target w hwall_le
        have hlen_er : er.2.length ≤ n := by
          have h1 : er.2.length ≤ ws.length := extendRange_length_le ws target w; omega
        rcases List.mem_cons.mp hv_in_l with rfl | hv_ws
        · -- v = w
          exact ⟨rangeFormula v er.1, List.mem_cons_self,
            (mem_rangeFormula_evalSet v er.1 Vn hle_er v).mpr ⟨hv_Vn, le_refl v, hle_er⟩⟩
        · by_cases hv_rest : v ∈ er.2
          · obtain ⟨φ, hφ, hv_φ⟩ := ih er.2 hlen_er
              (List.Pairwise.sublist (extendRange_snd_suffix ws target w).sublist hpw_lt')
              v hv_rest hv_target hv_Vn
            exact ⟨φ, List.mem_cons_of_mem _ hφ, hv_φ⟩
          · exact ⟨rangeFormula w er.1, List.mem_cons_self,
              (mem_rangeFormula_evalSet w er.1 Vn hle_er v).mpr
                ⟨hv_Vn, le_of_lt (hwall_lt v hv_ws),
                 extendRange_consumed_le_fst ws target w v hpw_le' hv_ws hv_rest⟩⟩
      case isFalse hmem_target =>
        rcases List.mem_cons.mp hv_in_l with rfl | hv_ws
        · exact absurd hv_target hmem_target
        · exact ih ws hlen_ws hpw_lt' v hv_ws hv_target hv_Vn

/-! ## Correctness of finsetToFormula -/

private theorem sort_pairwise_lt [LinearOrder V] (s : Finset V) :
    (s.sort (· ≤ ·)).Pairwise (· < ·) := by
  rw [List.pairwise_iff_get]; intro i j hij; exact Finset.sortedLT_sort s hij

/-- Evaluating the constructed formula against the repository gives back exactly
    the target set. -/
theorem finsetToFormula_eval [LinearOrder V]
    (repo : Finset V) (target : Finset V) (h : target.Nonempty) (hsub : target ⊆ repo) :
    (finsetToFormula repo target h).eval repo = target := by
  -- We prove the Set-level statement and then transfer via coe injectivity
  suffices hset : (finsetToFormula repo target h).evalSet (↑repo : Set V) = ↑target by
    apply Finset.coe_injective
    rw [eval_coe]
    exact hset
  set sorted := repo.sort (· ≤ ·) with hsorted_def
  set Vn : Set V := ↑repo
  have hpw_lt := sort_pairwise_lt repo
  have hmem_sort : ∀ v, v ∈ sorted ↔ v ∈ repo := fun v => Finset.mem_sort (· ≤ ·)
  -- Helper: extract formula membership from the match structure
  have fwd_extract : ∀ v, v ∈ (finsetToFormula repo target h).evalSet Vn →
      (∃ φ, φ ∈ buildRanges sorted target ∧ v ∈ φ.evalSet Vn) ∨ v ∈ target := by
    intro v hv_eval
    unfold finsetToFormula at hv_eval; simp only at hv_eval
    revert hv_eval
    match hm : buildRanges sorted target with
    | [] =>
      intro hv_eval
      right
      simp only [VersionFormula.evalSet, CmpOp.evalProp, Set.mem_sep_iff] at hv_eval
      rw [hv_eval.2]; exact Finset.min'_mem target h
    | [φ] =>
      intro hv_eval
      left; exact ⟨φ, List.mem_cons_self, hv_eval⟩
    | φ :: ψ :: ψs =>
      intro hv_eval
      left
      rw [disjoinFormulas_mem Vn v φ (ψ :: ψs)] at hv_eval
      obtain ⟨ψ', hψ', hv'⟩ := hv_eval
      exact ⟨ψ', hψ', hv'⟩
  -- Main proof
  ext v; simp only [Finset.mem_coe]
  constructor
  · -- Forward: v ∈ eval → v ∈ target
    intro hv_eval
    rcases fwd_extract v hv_eval with ⟨φ, hφ, hv_φ⟩ | hv_target
    · have hv_repo : v ∈ Vn := evalSet_subset φ Vn hv_φ
      have hv_sorted : v ∈ sorted := (hmem_sort v).mpr (Finset.mem_coe.mp hv_repo)
      exact buildRanges_sound sorted.length sorted le_rfl target Vn hpw_lt
        v hv_sorted φ hφ hv_φ
    · exact hv_target
  · -- Backward: v ∈ target → v ∈ eval
    intro hv_target
    have hv_repo : v ∈ repo := hsub hv_target
    have hv_sorted : v ∈ sorted := (hmem_sort v).mpr hv_repo
    have hv_Vn : v ∈ Vn := Finset.mem_coe.mpr hv_repo
    obtain ⟨φ, hφ, hv_φ⟩ := buildRanges_complete sorted.length sorted le_rfl target
      Vn hpw_lt v hv_sorted hv_target hv_Vn
    -- Construct membership from formula
    have hφ_ranges : φ ∈ buildRanges sorted target := hφ
    unfold finsetToFormula; simp only
    match hm : buildRanges sorted target, hφ_ranges with
    | [], hφ_ranges => exact absurd hφ_ranges List.not_mem_nil
    | [ψ], hφ_ranges =>
      have heq := List.mem_singleton.mp hφ_ranges
      subst heq; exact hv_φ
    | ψ₁ :: ψ₂ :: ψs, hφ_ranges =>
      exact (disjoinFormulas_mem Vn v ψ₁ (ψ₂ :: ψs)).mpr ⟨φ, hφ_ranges, hv_φ⟩

variable {N : Type*} [DecidableEq N]

/-! ## liftVFDeps: lift a core DepRel to VFDepRel -/

/-- Lift a concrete `DepRel` back to a `VFDepRel` by wrapping each version set
    into a `VersionFormula` via `finsetToFormula`. Each `(p, m, vs)` becomes
    `(p, m, φ)` where `φ` evaluates to `vs` against the repository. -/
def liftVFDeps [LinearOrder V] (R : Real N V) (Δ : DepRel N V) : VFDepRel N V :=
  Δ.image (fun ⟨p, m, vs⟩ =>
    if h : vs.Nonempty then
      (p, m, finsetToFormula (repoVersions R m) vs h)
    else
      -- empty version set: use .top as a fallback (should not occur in practice)
      (p, m, VersionFormula.top))

end PackageCalculus
