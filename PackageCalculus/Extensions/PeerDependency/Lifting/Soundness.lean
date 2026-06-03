import PackageCalculus.Extensions.PeerDependency.Lifting.Definition

namespace PackageCalculus.PeerDep

open PackageCalculus Concurrent

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {G : Type*} [DecidableEq G]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

/-! ## Lifting soundness & completeness -/

theorem liftResolution_soundness
    (R_C : Real N V) (Δ_C : DepRel N V) (Θ : PeerRel N V)
    (g : V → G) (r : Package N V)
    (S' : Finset (Package N' V'))
    (hres : IsResolution (peerReal R_C Δ_C Θ g) (peerDeps Δ_C Θ g)
      (Concurrent.embedPkg g r) S') :
    ∃ π, IsPeerResolution R_C Δ_C Θ g r (liftResolution g S') π := by
  have hsound := peer_soundness R_C Δ_C Θ g r S' hres
  suffices heq : liftResolution g S' = S'.preimage (Concurrent.embedPkg g)
      (Set.InjOn.mono (Set.subset_univ _)
        (Function.Injective.injOn (embedPkgFn_injective g))) by
    rw [heq]; exact ⟨_, hsound⟩
  ext p; simp only [liftResolution, Finset.mem_filterMap, Finset.mem_preimage]
  constructor
  · rintro ⟨p', hp', hinv⟩
    have := tryInvPkg_some g (Option.mem_def.mpr hinv)
    rwa [this]
  · intro hp; exact ⟨Concurrent.embedPkg g p, hp, Option.mem_def.mpr (tryInvPkg_embed g p)⟩


end PackageCalculus.PeerDep
