import PackageCalculus.Extensions.PackageFormula.Reduction.Completeness
import PackageCalculus.Extensions.PackageFormula.Reduction.Soundness

namespace PackageCalculus.PkgFormula

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hpn : HasPFNames N V N'] [hpv : Conflict.HasConflictVersions V V']

def embedPkgFn : Package N V → Package N' V' :=
  fun p => (hpn.origN p.1, hpv.origV p.2)

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem embedPkgFn_eq_embedPkg : (embedPkgFn : Package N V → Package N' V') = embedPkg :=
  rfl

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem embedPkgFn_injective :
    Function.Injective (embedPkgFn : Package N V → Package N' V') := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [embedPkgFn, Prod.mk.injEq] at h
  exact Prod.ext (hpn.origN.injective h.1) (hpv.origV.injective h.2)

def tryInvPkg (p : Package N' V') : Option (Package N V) :=
  match hpn.tryOrigN p.1, hpv.tryOrigV p.2 with
  | some n, some v => some (n, v)
  | _, _ => none

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem tryInvPkg_embed (p : Package N V) :
    tryInvPkg (embedPkgFn p) = some p := by
  simp [tryInvPkg, embedPkgFn, hpn.tryOrigN_origN, hpv.tryOrigV_origV]

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem tryInvPkg_some {p' : Package N' V'} {p : Package N V}
    (h : p ∈ tryInvPkg p') : embedPkgFn p = p' := by
  obtain ⟨n', v'⟩ := p'; obtain ⟨n, v⟩ := p
  simp only [tryInvPkg, Option.mem_def, embedPkgFn] at h ⊢
  generalize htn : hpn.tryOrigN n' = on at h
  generalize htv : hpv.tryOrigV v' = ov at h
  match on, ov with
  | some n₀, some v₀ =>
    simp at h; obtain ⟨rfl, rfl⟩ := h
    show (hpn.origN n₀, hpv.origV v₀) = (n', v')
    rw [hpn.tryOrigN_some _ _ htn, hpv.tryOrigV_some _ _ htv]
  | some _, none => simp at h
  | none, _ => simp at h

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
private theorem tryInvPkg_inj :
    ∀ a a' (b : Package N V), b ∈ tryInvPkg a → b ∈ tryInvPkg a' → a = a' := by
  intro a a' b ha ha'
  exact (tryInvPkg_some ha).symm.trans (tryInvPkg_some ha')

/-! ## Lift functions -/

def liftReal (R' : Real N' V') : Real N V :=
  R'.filterMap tryInvPkg tryInvPkg_inj

def liftResolution (S' : Finset (Package N' V')) : Finset (Package N V) :=
  S'.filterMap tryInvPkg tryInvPkg_inj

/-! ## Membership lemmas -/

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem mem_liftReal {R' : Real N' V'} {p : Package N V} :
    p ∈ liftReal R' ↔ embedPkg p ∈ R' := by
  simp only [liftReal, Finset.mem_filterMap, ← embedPkgFn_eq_embedPkg]
  constructor
  · rintro ⟨_, hp', hinv⟩; exact tryInvPkg_some hinv ▸ hp'
  · exact fun hp => ⟨_, hp, tryInvPkg_embed p⟩

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem mem_liftResolution {S' : Finset (Package N' V')} {p : Package N V} :
    p ∈ liftResolution S' ↔ embedPkg p ∈ S' := by
  simp only [liftResolution, Finset.mem_filterMap, ← embedPkgFn_eq_embedPkg]
  constructor
  · rintro ⟨_, hp', hinv⟩; exact tryInvPkg_some hinv ▸ hp'
  · exact fun hp => ⟨_, hp, tryInvPkg_embed p⟩


end PackageCalculus.PkgFormula
