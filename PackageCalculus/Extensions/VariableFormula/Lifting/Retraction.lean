import PackageCalculus.Extensions.VariableFormula.Lifting.Definition

namespace PackageCalculus.VarFormula

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {X : Type*} [DecidableEq X] {Y : Type*} [DecidableEq Y]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVFNames N V X Y N'] [hvv : HasVFVersions V Y V']

/-! ## Round-trip theorems -/

theorem liftReal_vfReal [LT Y] [DecidableRel (· < · : Y → Y → Prop)] [Fintype X]
    (Y_x : X → Finset Y) (R : Real N V) (Δ_Ψ : VFDepRel N V X Y) :
    liftReal (X := X) (Y := Y) (vfReal (N' := N') (V' := V') Y_x R Δ_Ψ) = R := by
  ext p;
  convert mem_liftReal;
  unfold vfReal;
  simp +decide [ embedPkg ];
  exact fun _ _ _ _ h => False.elim ( witnessPackages_not_orig' _ _ _ _ h )


end PackageCalculus.VarFormula
