import PackageCalculus.Extensions.Feature.Reduction.Completeness
import PackageCalculus.Extensions.Feature.Reduction.Soundness

namespace PackageCalculus.Feature

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {F : Type*} [DecidableEq F] [Fintype F]
variable {N' : Type*} [DecidableEq N'] [hfn : HasFeatureNames N F N']

/-! ## Computable inverse helpers -/

def tryInvPkg (p : Package N' V) : Option (Package N V) :=
  match hfn.tryOrigN p.1 with
  | some n => some (n, p.2)
  | none => none

attribute [local simp] HasFeatureNames.tryOrigN_origN

omit [DecidableEq N] [DecidableEq V] [DecidableEq F] [Fintype F] [DecidableEq N'] in
private theorem tryInvPkg_embed (p : Package N V) :
    tryInvPkg (hfn := hfn) (embedPkg F p) = some p := by
  simp [tryInvPkg, embedPkg, hfn.tryOrigN_origN]

omit [DecidableEq N] [DecidableEq V] [DecidableEq F] [Fintype F] [DecidableEq N'] in
theorem tryInvPkg_some {p' : Package N' V} {p : Package N V}
    (h : p ∈ tryInvPkg (hfn := hfn) p') : embedPkg F p = p' := by
  obtain ⟨n', v'⟩ := p'
  obtain ⟨n, v⟩ := p
  simp only [tryInvPkg, Option.mem_def, embedPkg] at h ⊢
  generalize htn : hfn.tryOrigN n' = on at h
  match on with
  | some n₀ =>
    simp at h; obtain ⟨rfl, rfl⟩ := h
    show (hfn.origN n₀, v') = (n', v')
    rw [hfn.tryOrigN_some _ _ htn]
  | none => simp at h

omit [DecidableEq N] [DecidableEq V] [DecidableEq F] [Fintype F] [DecidableEq N'] in
private theorem tryInvPkg_inj :
    ∀ a a' (b : Package N V), b ∈ tryInvPkg (hfn := hfn) a → b ∈ tryInvPkg (hfn := hfn) a' → a = a' := by
  intro a a' b ha ha'
  exact (tryInvPkg_some ha).symm.trans (tryInvPkg_some ha')

/-! ## Lift functions -/

/-- Lift an extended-space repository back to the original space. -/
def liftReal (R' : Real N' V) : Real N V :=
  R'.filterMap (tryInvPkg (hfn := hfn)) tryInvPkg_inj

/-- Lift an extended-space resolution back to a feature resolution.
    Each original package is paired with the set of features active for it. -/
def liftResolution (S' : Finset (Package N' V)) :
    Finset (Package N V × Finset F) :=
  (S'.filterMap (tryInvPkg (hfn := hfn)) tryInvPkg_inj).image
    (fun p => (p, Finset.univ.filter (fun f => (hfn.featuredN p.1 f, p.2) ∈ S')))

/-! ## Membership lemmas -/

omit [DecidableEq N] [DecidableEq V] [DecidableEq F] [Fintype F] [DecidableEq N'] in
theorem mem_liftReal {R' : Real N' V} {p : Package N V} :
    p ∈ liftReal (hfn := hfn) R' ↔ embedPkg F p ∈ R' := by
  simp only [liftReal, Finset.mem_filterMap]
  constructor
  · rintro ⟨p', hp', hinv⟩
    exact (tryInvPkg_some hinv) ▸ hp'
  · intro hp
    exact ⟨embedPkg F p, hp, by rw [tryInvPkg_embed]⟩

theorem mem_liftResolution' {S' : Finset (Package N' V)}
    {n : N} {v : V} (h : (hfn.origN n, v) ∈ S') :
    ((n, v), Finset.univ.filter (fun f => (hfn.featuredN n f, v) ∈ S')) ∈
      liftResolution (hfn := hfn) S' := by
  simp only [liftResolution, Finset.mem_image, Finset.mem_filterMap]
  exact ⟨(n, v), ⟨(hfn.origN n, v), h, by simp [tryInvPkg, hfn.tryOrigN_origN]⟩, rfl⟩

theorem liftResolution_elim {S' : Finset (Package N' V)}
    {pfs : Package N V × Finset F} (h : pfs ∈ liftResolution (hfn := hfn) S') :
    ∃ n v, (hfn.origN n, v) ∈ S' ∧
      pfs = ((n, v), Finset.univ.filter (fun f => (hfn.featuredN n f, v) ∈ S')) := by
  simp only [liftResolution, Finset.mem_image, Finset.mem_filterMap] at h
  obtain ⟨⟨n, v⟩, ⟨p', hp', hinv⟩, rfl⟩ := h
  have heq := tryInvPkg_some hinv
  simp only [embedPkg] at heq
  refine ⟨n, v, ?_, rfl⟩
  exact heq ▸ hp'


end PackageCalculus.Feature
