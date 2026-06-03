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
theorem liftVFDeps_soundness [LinearOrder V]
    (R : Real N V) (Δ : DepRel N V) (r : Package N V) (S : Finset (Package N V))
    (hne : ∀ p m vs, (p, m, vs) ∈ Δ → vs.Nonempty)
    (hsub : ∀ p m vs, (p, m, vs) ∈ Δ → vs ⊆ repoVersions R m)
    (hres : IsResolution R Δ r S) :
    IsVFResolution R (liftVFDeps R Δ) r S := by
  rw [← vfReduction_correct]
  rw [liftVFDeps_vfReduce R Δ hne hsub]
  exact hres

end PackageCalculus
