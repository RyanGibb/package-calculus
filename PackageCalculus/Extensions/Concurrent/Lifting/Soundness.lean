import PackageCalculus.Extensions.Concurrent.Lifting.Definition

namespace PackageCalculus.Concurrent

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {G : Type*} [DecidableEq G]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

/-! ## Lifting soundness & completeness -/

theorem liftResolution_soundness
    (R_C : Real N V) (Δ_C : DepRel N V)
    (g : V → G) (r : Package N V)
    (S' : Finset (Package N' V'))
    (hres : IsResolution (concurrentReal R_C Δ_C g) (concurrentDeps Δ_C g)
      (embedPkg g r) S')
    (hfunc : Δ_C.FunctionalInName) :
    ∃ π, IsConcurrentResolution R_C Δ_C g r (liftResolution g S') π := by
  have hsound := concurrent_soundness R_C Δ_C g r S' hres hfunc
  -- The preimageS used internally equals our liftResolution extensionally
  suffices heq : liftResolution g S' = S'.preimage (embedPkg g)
      (Set.InjOn.mono (Set.subset_univ _)
        (Function.Injective.injOn (embedPkgFn_injective g))) by
    rw [heq]; exact ⟨_, hsound⟩
  ext p; simp [mem_liftResolution, Finset.mem_preimage]


end PackageCalculus.Concurrent
