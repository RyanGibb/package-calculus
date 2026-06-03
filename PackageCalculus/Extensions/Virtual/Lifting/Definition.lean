import PackageCalculus.Extensions.Virtual.Reduction.Completeness
import PackageCalculus.Extensions.Virtual.Reduction.Soundness

namespace PackageCalculus.Virtual

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVirtualNames N V N'] [hvv : HasVirtualVersions N V V']

/-! ## Lift functions -/

def embedPkgFn : Package N V → Package N' V' :=
  fun p => (hvn.origN p.1, hvv.origV p.2)

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem embedPkgFn_eq_embedPkg :
    (embedPkgFn : Package N V → Package N' V') = embedPkg :=
  rfl

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem embedPkgFn_injective :
    Function.Injective (embedPkgFn : Package N V → Package N' V') := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [embedPkgFn, Prod.mk.injEq] at h
  exact Prod.ext (hvn.origN.injective h.1) (hvv.origV.injective h.2)

def tryInvPkg (p : Package N' V') : Option (Package N V) :=
  match hvn.tryOrigN p.1, hvv.tryOrigV p.2 with
  | some n, some v => some (n, v)
  | _, _ => none

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
private theorem tryInvPkg_inj :
    ∀ a a' (b : Package N V), b ∈ tryInvPkg a → b ∈ tryInvPkg a' → a = a' := by
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

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem tryInvPkg_embed (p : Package N V) :
    tryInvPkg (embedPkgFn p) = some p := by
  simp [tryInvPkg, embedPkgFn, hvn.tryOrigN_origN, hvv.tryOrigV_origV]

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem tryInvPkg_some {p' : Package N' V'} {p : Package N V}
    (h : p ∈ tryInvPkg p') : embedPkgFn p = p' := by
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

def liftReal (R' : Real N' V') : Real N V :=
  R'.filterMap tryInvPkg tryInvPkg_inj

def liftResolution (S' : Finset (Package N' V')) : Finset (Package N V) :=
  S'.filterMap tryInvPkg tryInvPkg_inj

/-! ## Membership lemmas -/

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem mem_liftReal {R' : Real N' V'} {p : Package N V} :
    p ∈ liftReal R' ↔ embedPkg p ∈ R' := by
  simp only [liftReal, Finset.mem_filterMap]
  constructor
  · rintro ⟨p', hp', hinv⟩
    have heq := tryInvPkg_some hinv; rw [embedPkgFn_eq_embedPkg] at heq; rwa [heq]
  · intro hp
    exact ⟨embedPkg p, hp, by show p ∈ tryInvPkg (embedPkgFn p); rw [tryInvPkg_embed]; rfl⟩

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem mem_liftResolution {S' : Finset (Package N' V')} {p : Package N V} :
    p ∈ liftResolution S' ↔ embedPkg p ∈ S' := by
  simp only [liftResolution, Finset.mem_filterMap]
  constructor
  · rintro ⟨p', hp', hinv⟩
    have heq := tryInvPkg_some hinv; rw [embedPkgFn_eq_embedPkg] at heq; rwa [heq]
  · intro hp
    exact ⟨embedPkg p, hp, by show p ∈ tryInvPkg (embedPkgFn p); rw [tryInvPkg_embed]; rfl⟩


end PackageCalculus.Virtual
