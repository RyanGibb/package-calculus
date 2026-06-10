import PackageCalculus.Extensions.Concurrent.Reduction.Completeness
import PackageCalculus.Extensions.Concurrent.Reduction.Soundness

namespace PackageCalculus.Concurrent

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {G : Type*} [DecidableEq G]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

private def embedPkgFn (g : V → G) : Package N V → Package N' V' :=
  fun p => (hcnm.granularN p.1 (g p.2), hcvr.origV p.2)

theorem embedPkgFn_injective (g : V → G) :
    Function.Injective (embedPkgFn g : Package N V → Package N' V') := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [embedPkgFn, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have ⟨hn, _⟩ := hcnm.granularN_injective h1
  exact Prod.ext hn (hcvr.origV.injective h2)

private def tryInvPkg (g : V → G) (p' : Package N' V') : Option (Package N V) :=
  match hcvr.tryOrigV p'.2 with
  | some v =>
    match hcnm.tryGranularN p'.1 with
    | some (n, g') => if g v = g' then some (n, v) else none
    | none => none
  | none => none

theorem tryInvPkg_embed (g : V → G) (p : Package N V) :
    tryInvPkg g (embedPkg g p) = some p := by
  simp only [tryInvPkg, embedPkg, hcvr.tryOrigV_origV, hcnm.tryGranularN_granularN, ite_true]

theorem tryInvPkg_some (g : V → G) {p' : Package N' V'} {p : Package N V}
    (h : p ∈ tryInvPkg g p') : embedPkg g p = p' := by
  obtain ⟨n, v⟩ := p; obtain ⟨n', v'⟩ := p'
  simp only [tryInvPkg, Option.mem_def] at h
  generalize hv : hcvr.tryOrigV v' = ov at h
  generalize hg : hcnm.tryGranularN n' = og at h
  match ov, og with
  | some v₀, some ng =>
    simp only at h
    split at h
    · rename_i heq_g
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [embedPkg, Prod.mk.injEq]
      exact ⟨by rw [heq_g]; exact hcnm.tryGranularN_some _ _ hg,
             hcvr.tryOrigV_some _ _ hv⟩
    · simp at h
  | some _, none => simp at h
  | none, _ => simp at h

private theorem tryInvPkg_inj (g : V → G) :
    ∀ a a' (b : Package N V), b ∈ tryInvPkg g a → b ∈ tryInvPkg g a' → a = a' := by
  intro a a' b ha ha'
  exact (tryInvPkg_some g ha).symm.trans (tryInvPkg_some g ha')

/-! ## Lift functions -/

def liftReal (g : V → G) (R' : Real N' V') : Real N V :=
  R'.filterMap (tryInvPkg g) (tryInvPkg_inj g)

def liftResolution (g : V → G) (S' : Finset (Package N' V')) :
    Finset (Package N V) :=
  S'.filterMap (tryInvPkg g) (tryInvPkg_inj g)

/-! ## Membership lemmas -/

theorem mem_liftReal {g : V → G} {R' : Real N' V'} {p : Package N V} :
    p ∈ liftReal g R' ↔ embedPkg g p ∈ R' := by
  simp only [liftReal, Finset.mem_filterMap]
  constructor
  · rintro ⟨_, hp', hinv⟩
    exact (tryInvPkg_some g (Option.mem_def.mpr hinv)) ▸ hp'
  · exact fun hp => ⟨_, hp, Option.mem_def.mpr (tryInvPkg_embed g p)⟩

theorem mem_liftResolution {g : V → G} {S' : Finset (Package N' V')} {p : Package N V} :
    p ∈ liftResolution g S' ↔ embedPkg g p ∈ S' := by
  simp only [liftResolution, Finset.mem_filterMap]
  constructor
  · rintro ⟨_, hp', hinv⟩
    exact (tryInvPkg_some g (Option.mem_def.mpr hinv)) ▸ hp'
  · exact fun hp => ⟨_, hp, Option.mem_def.mpr (tryInvPkg_embed g p)⟩


end PackageCalculus.Concurrent
