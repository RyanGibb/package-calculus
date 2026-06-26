import PackageCalculus.Extensions.VariableFormula.Lifting.Definition

namespace PackageCalculus.VarFormula

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {X : Type*} [DecidableEq X] {Y : Type*} [DecidableEq Y]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVFNames N V X Y N'] [hvv : HasVFVersions V Y V']

/-! ## Lifting soundness & completeness -/

theorem liftResolution_soundness
    [LT Y] [DecidableRel (· < · : Y → Y → Prop)] [Fintype X] [Nonempty Y]
    (Y_x : X → Finset Y)
    (R_Ψ : Real N V) (Δ_Ψ : VFDepRel N V X Y)
    (r : Package N V) (S' : Finset (Package N' V'))
    (hres : IsResolution (vfReal Y_x R_Ψ Δ_Ψ) (vfDeps Y_x Δ_Ψ)
      (embedPkg (X := X) (Y := Y) r) S') :
    IsVFResolution R_Ψ Δ_Ψ r (liftResolution (X := X) (Y := Y) S')
      (extractAssignment (N := N) (V := V) (X := X) (Y := Y) S') := by
  have hsound := variable_formula_soundness Y_x R_Ψ Δ_Ψ r S' hres
  -- Show liftResolution and preimageS agree
  suffices heq : liftResolution (X := X) (Y := Y) S' =
      S'.preimage (embedPkg (X := X) (Y := Y))
      (Set.InjOn.mono (Set.subset_univ _)
        (Function.Injective.injOn (embedPkgFn_injective (X := X) (Y := Y)))) by
    rw [heq]; exact hsound
  ext p; simp [← embedPkgFn_eq_embedPkg, mem_liftResolution, Finset.mem_preimage]


end PackageCalculus.VarFormula
