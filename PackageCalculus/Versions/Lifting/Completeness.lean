import PackageCalculus.Versions.Lifting.Definition
import PackageCalculus.Versions.Lifting.Retraction
import PackageCalculus.Versions.Reduction.Correctness

set_option linter.unusedSectionVars false

namespace PackageCalculus

variable {V : Type*} [DecidableEq V]
variable {N : Type*} [DecidableEq N]

/-- If `S` is a VF-resolution for the lifted deps, it is a resolution for
    the original concrete `Δ`. -/
theorem liftResolution_completeness [LinearOrder V]
    (R : Real N V) (Δ : DepRel N V) (r : Package N V) (S : Finset (Package N V))
    (hres : IsVFResolution R (liftVFDeps R Δ) r S) :
    IsResolution R Δ r S := by
  have h := (version_formula_correct R (liftVFDeps R Δ) r S).mpr hres
  rw [liftVFDeps_vfReduce R Δ] at h
  exact (restrictReal_resolution_iff R Δ r S).mp h

end PackageCalculus
