import PackageCalculus.Extensions.Conflict.Lifting.Definition

namespace PackageCalculus.Conflict

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcn : HasConflictNames N V N'] [hcv : HasConflictVersions V V']

/-! ## Lifting soundness & completeness -/

theorem liftResolution_soundness
    (R : Real N V) (Δ : DepRel N V) (Γ : ConflictRel N V)
    (r : Package N V) (S' : Finset (Package N' V'))
    (hres : IsResolution (conflictReal R Γ) (conflictDeps Δ Γ) (embedPkg r) S') :
    IsConflictResolution R Δ Γ r (liftResolution S') := by
  convert conflict_soundness R Δ Γ r S' hres

end PackageCalculus.Conflict