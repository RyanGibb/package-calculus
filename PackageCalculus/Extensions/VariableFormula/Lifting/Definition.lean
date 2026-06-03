import PackageCalculus.Extensions.VariableFormula.Reduction.Completeness
import PackageCalculus.Extensions.VariableFormula.Reduction.Soundness
import Mathlib

namespace PackageCalculus.VarFormula

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {X : Type*} [DecidableEq X] {Y : Type*} [DecidableEq Y]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVFNames N V X Y N'] [hvv : HasVFVersions V Y V']

def embedPkgFn : Package N V → Package N' V' :=
  fun p => (hvn.origN p.1, hvv.origV p.2)

omit [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
  [DecidableEq N'] [DecidableEq V'] in
theorem embedPkgFn_eq_embedPkg :
    (embedPkgFn (X := X) (Y := Y) : Package N V → Package N' V') =
      embedPkg (X := X) (Y := Y) :=
  rfl

omit [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
  [DecidableEq N'] [DecidableEq V'] in
theorem embedPkgFn_injective :
    Function.Injective (embedPkgFn (X := X) (Y := Y) :
      Package N V → Package N' V') := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [embedPkgFn, Prod.mk.injEq] at h
  exact Prod.ext (hvn.origN.injective h.1) (hvv.origV.injective h.2)

/-! ## Computable inverse helpers -/

def tryInvPkg (p : Package N' V') : Option (Package N V) :=
  match hvn.tryOrigN p.1, hvv.tryOrigV p.2 with
  | some n, some v => some (n, v)
  | _, _ => none

omit [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
  [DecidableEq N'] [DecidableEq V'] in
private theorem tryInvPkg_inj :
    ∀ a a' (b : Package N V), b ∈ tryInvPkg (hvn := hvn) (hvv := hvv) a →
      b ∈ tryInvPkg (hvn := hvn) (hvv := hvv) a' → a = a' := by
  intro a a' ⟨n, v⟩ h1 h2
  simp only [tryInvPkg, Option.mem_def] at h1 h2
  revert h1 h2
  cases hn1 : hvn.tryOrigN a.1 <;> cases hv1 : hvv.tryOrigV a.2 <;> simp (config := { decide := false })
  intro rfl rfl
  cases hn2 : hvn.tryOrigN a'.1 <;> cases hv2 : hvv.tryOrigV a'.2 <;> simp (config := { decide := false })
  intro rfl rfl
  exact Prod.ext
    ((hvn.tryOrigN_some _ _ hn1).symm.trans (hvn.tryOrigN_some _ _ hn2))
    ((hvv.tryOrigV_some _ _ hv1).symm.trans (hvv.tryOrigV_some _ _ hv2))

omit [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
  [DecidableEq N'] [DecidableEq V'] in
theorem tryInvPkg_embed (p : Package N V) :
    tryInvPkg (hvn := hvn) (hvv := hvv) (embedPkgFn (X := X) (Y := Y) p) = some p := by
  simp [tryInvPkg, embedPkgFn, hvn.tryOrigN_origN, hvv.tryOrigV_origV]

omit [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
  [DecidableEq N'] [DecidableEq V'] in
theorem tryInvPkg_some {p' : Package N' V'} {p : Package N V}
    (h : p ∈ tryInvPkg (hvn := hvn) (hvv := hvv) p') :
    embedPkgFn (X := X) (Y := Y) p = p' := by
  obtain ⟨n', v'⟩ := p'; obtain ⟨n, v⟩ := p
  simp only [tryInvPkg, Option.mem_def, embedPkgFn] at h ⊢
  generalize htn : hvn.tryOrigN n' = on at h
  generalize htv : hvv.tryOrigV v' = ov at h
  match on, ov with
  | some n₀, some v₀ =>
    simp at h; obtain ⟨rfl, rfl⟩ := h
    show (hvn.origN n₀, hvv.origV v₀) = (n', v')
    rw [hvn.tryOrigN_some _ _ htn, hvv.tryOrigV_some _ _ htv]
  | some _, none => simp at h
  | none, _ => simp at h

/-! ## Lift functions -/

def liftReal (R' : Real N' V') : Real N V :=
  R'.filterMap (tryInvPkg (X := X) (Y := Y) (hvn := hvn) (hvv := hvv)) tryInvPkg_inj

def liftResolution (S' : Finset (Package N' V')) : Finset (Package N V) :=
  S'.filterMap (tryInvPkg (X := X) (Y := Y) (hvn := hvn) (hvv := hvv)) tryInvPkg_inj

/-! ## Membership lemmas -/

omit [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
  [DecidableEq N'] [DecidableEq V'] in
theorem mem_liftReal {R' : Real N' V'} {p : Package N V} :
    p ∈ liftReal (X := X) (Y := Y) R' ↔ embedPkg (X := X) (Y := Y) p ∈ R' := by
  simp only [liftReal, Finset.mem_filterMap]
  constructor
  · rintro ⟨p', hp', hinv⟩
    have heq := tryInvPkg_some hinv
    rw [embedPkgFn_eq_embedPkg] at heq; rwa [heq]
  · intro hp
    exact ⟨embedPkg (X := X) (Y := Y) p, hp, by
      show p ∈ tryInvPkg (embedPkgFn (X := X) (Y := Y) p)
      rw [tryInvPkg_embed]; rfl⟩

omit [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
  [DecidableEq N'] [DecidableEq V'] in
theorem mem_liftResolution {S' : Finset (Package N' V')} {p : Package N V} :
    p ∈ liftResolution (X := X) (Y := Y) S' ↔ embedPkg (X := X) (Y := Y) p ∈ S' := by
  simp only [liftResolution, Finset.mem_filterMap]
  constructor
  · rintro ⟨p', hp', hinv⟩
    have heq := tryInvPkg_some hinv
    rw [embedPkgFn_eq_embedPkg] at heq; rwa [heq]
  · intro hp
    exact ⟨embedPkg (X := X) (Y := Y) p, hp, by
      show p ∈ tryInvPkg (embedPkgFn (X := X) (Y := Y) p)
      rw [tryInvPkg_embed]; rfl⟩

/-! ## Auxiliary: witnessPackages and witnessSet produce non-orig names -/

omit [DecidableEq N] [DecidableEq V] [DecidableEq X] in
theorem witnessPackages_not_orig'
    [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (p : Package N' V') (ψ : Formula N V X Y) (n : N) (v : V') :
    (hvn.origN n, v) ∉ witnessPackages p ψ := by
  by_contra h_contra;
  induction' h : Formula.weight ψ using Nat.strong_induction_on with w hw generalizing ψ p;
  rcases ψ with ( _ | ⟨ ψ_L, ψ_R ⟩ | ⟨ ψ_L, ψ_R ⟩ | ⟨ x, ω, y ⟩ | ⟨ n, vs ⟩ );
  all_goals simp +decide [ witnessPackages ] at h_contra;
  · rcases h_contra with ( h_contra | h_contra );
    · exact hw _ ( by simp +decide [ Formula.weight ] at h ⊢; linarith ) _ _ h_contra rfl;
    · exact hw _ ( by rw [ show ( ψ_L.conj ψ_R ).weight = ψ_L.weight + ψ_R.weight + 2 from rfl ] at h; linarith ) _ _ h_contra rfl;
  · rcases h_contra with ( h_contra | h_contra );
    · exact hw _ ( by simp +decide [ Formula.weight ] at h ⊢; linarith ) _ _ h_contra rfl;
    · exact hw _ ( by simp +decide [ Formula.weight ] at h ⊢; linarith ) _ _ h_contra rfl;
  · rcases h_contra with ( h_contra | h_contra );
    · exact hw _ ( by simp +decide [ Formula.weight ] at h ⊢; linarith ) _ _ h_contra rfl;
    · exact hw _ ( by simp +decide [ Formula.weight ] at h ⊢; linarith ) _ _ h_contra rfl;
  · rcases h_contra with ( h_contra | h_contra );
    · exact hw _ ( by simp +decide [ Formula.weight ] at h ⊢; linarith ) _ _ h_contra rfl;
    · exact hw _ ( by simp +decide [ Formula.weight ] at h ⊢; linarith ) _ _ h_contra rfl;
  · exact hw _ ( by linarith [ show Formula.weight ‹_› < w from by linarith [ show Formula.weight ( Formula.neg ( Formula.neg ‹_› ) ) = 3 * ( Formula.weight ( Formula.neg ‹_› ) + 1 ) from rfl, show Formula.weight ( Formula.neg ‹_› ) = 3 * ( Formula.weight ‹_› + 1 ) from rfl ] ] ) _ _ h_contra rfl


end PackageCalculus.VarFormula
