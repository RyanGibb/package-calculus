import PackageCalculus.Extensions.Virtual.Lifting.Definition

namespace PackageCalculus.Virtual

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVirtualNames N V N'] [hvv : HasVirtualVersions N V V']

/-! ## Round-trip theorems -/

theorem liftReal_virtualReal (R : Real N V) (Δ : DepRel N V)
    (prov : ProvidesRel N V) :
    liftReal (virtualReal (N' := N') (V' := V') R Δ prov) = R := by
  convert Set.ext _;
  rotate_left;
  exact Package N V;
  exact { p : Package N V | embedPkg p ∈ virtualReal R Δ prov };
  exact { p : Package N V | p ∈ R };
  · unfold virtualReal;
    simp +decide [ embedSet, embedPkg ];
    grind +suggestions;
  · simp +decide [ Finset.ext_iff, Set.ext_iff, mem_liftReal ]

end PackageCalculus.Virtual