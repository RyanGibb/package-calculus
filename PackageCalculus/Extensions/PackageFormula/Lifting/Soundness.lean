import PackageCalculus.Extensions.PackageFormula.Lifting.Definition

namespace PackageCalculus.PkgFormula

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hpn : HasPFNames N V N'] [hpv : Conflict.HasConflictVersions V V']

/-! ## Lifting soundness & completeness -/

theorem liftResolution_soundness
    (R_Ψ : Real N V) (Δ_Ψ : PFDepRel N V)
    (r : Package N V) (S' : Finset (Package N' V'))
    (hres : IsResolution (pfReal R_Ψ Δ_Ψ) (pfDeps Δ_Ψ) (embedPkg r) S') :
    IsPFResolution R_Ψ Δ_Ψ r (liftResolution S') := by
  have h := pkgFormula_soundness R_Ψ Δ_Ψ r S' hres
  suffices heq : liftResolution S' = S'.preimage embedPkg
      (Set.InjOn.mono (Set.subset_univ _)
        (Function.Injective.injOn embedPkgFn_injective)) by
    rw [heq]; exact h
  ext p; simp [← embedPkgFn_eq_embedPkg, mem_liftResolution, Finset.mem_preimage]


end PackageCalculus.PkgFormula
