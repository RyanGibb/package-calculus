import PackageCalculus.Versions.Lifting.Definition
import PackageCalculus.Versions.Lifting.Retraction
import PackageCalculus.Versions.Reduction.Correctness

set_option linter.unusedSectionVars false

namespace PackageCalculus

variable {V : Type*} [DecidableEq V]
variable {N : Type*} [DecidableEq N]

/-! ## Lifting soundness & completeness -/

/-- If `S` is a resolution for the concrete `Δ`, it is also a resolution for the
    lifted `VFDepRel`. -/
theorem liftResolution_soundness [LinearOrder V]
    (R : Real N V) (Δ : DepRel N V) (r : Package N V) (S : Finset (Package N V))
    (hne : Δ.NonEmpty)
    (hsub : Δ.DependeesExist R)
    (hres : IsResolution R Δ r S) :
    IsVFResolution R (liftVFDeps R Δ) r S := by
  rw [← version_formula_correct]
  rw [liftVFDeps_vfReduce R Δ hne hsub]
  exact hres

end PackageCalculus
