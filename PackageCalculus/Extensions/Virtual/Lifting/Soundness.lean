import PackageCalculus.Extensions.Virtual.Lifting.Definition

namespace PackageCalculus.Virtual

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVirtualNames N V N'] [hvv : HasVirtualVersions N V V']

/-! ## Lifting soundness -/

theorem liftResolution_soundness
    (R_v : Real N V) (Delta_v : DepRel N V)
    (prov : ProvidesRel N V) (r : Package N V)
    (S' : Finset (Package N' V'))
    (hres : IsResolution (virtualReal R_v Delta_v prov) (virtualDeps Delta_v R_v prov)
      (embedPkg r) S') :
    ∃ rho, IsVirtualResolution R_v Delta_v prov r (liftResolution S') rho := by
  have hsound := virtual_soundness R_v Delta_v prov r S' hres
  suffices heq : liftResolution S' = S'.preimage embedPkg
      (Set.InjOn.mono (Set.subset_univ _)
        (Function.Injective.injOn embedPkgFn_injective)) by
    rw [heq]; exact ⟨_, hsound⟩
  ext p; simp only [liftResolution, Finset.mem_filterMap, Finset.mem_preimage]
  constructor
  · rintro ⟨p', hp', hinv⟩
    have heq := tryInvPkg_some hinv
    rw [embedPkgFn_eq_embedPkg] at heq; rwa [heq]
  · intro hp
    exact ⟨embedPkg p, hp, by
      show p ∈ tryInvPkg (embedPkgFn p)
      rw [tryInvPkg_embed]; rfl⟩


end PackageCalculus.Virtual
