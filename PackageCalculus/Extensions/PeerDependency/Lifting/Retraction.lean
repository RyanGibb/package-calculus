import PackageCalculus.Extensions.PeerDependency.Lifting.Definition

namespace PackageCalculus.PeerDep

open PackageCalculus Concurrent

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {G : Type*} [DecidableEq G]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

/-! ## Round-trip theorems -/

theorem liftReal_peerReal (R : Real N V) (Δ : DepRel N V)
    (Θ : PeerRel N V) (g : V → G) :
    liftReal g (peerReal (N' := N') (V' := V') R Δ Θ g) = R := by
  ext p;
  rw [ mem_liftReal, peerReal ];
  simp +decide [ embedPkg, embedReal ];
  constructor;
  · rintro (⟨ a, ha, ha' ⟩ | ⟨ a, b, a₁, b₁, _, a₂, _, a₃, b₂, _, hmem ⟩);
    · have := hcnm.granularN_injective ha'; aesop;
    · split at hmem;
      · simp only [Finset.mem_image] at hmem;
        obtain ⟨ w, _, hw ⟩ := hmem;
        rw [Prod.ext_iff] at hw;
        exact absurd hw.1 (hcnm.intermediateN_ne_granularN _ _ _ _ _);
      · simp at hmem;
  · exact fun hp => Or.inl ⟨ p.1, hp, rfl ⟩

end PackageCalculus.PeerDep