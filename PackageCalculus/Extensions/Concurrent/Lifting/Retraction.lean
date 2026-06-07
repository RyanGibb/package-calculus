import PackageCalculus.Extensions.Concurrent.Lifting.Definition

namespace PackageCalculus.Concurrent

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {G : Type*} [DecidableEq G]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

/-! ## Round-trip theorems -/

theorem liftReal_concurrentReal (R : Real N V) (Δ : DepRel N V) (g : V → G) :
    liftReal g (concurrentReal (N' := N') (V' := V') R Δ g) = R := by
  ext p;
  rw [ mem_liftReal, concurrentReal ];
  simp +decide [ embedReal, embedPkg ];
  constructor;
  · rintro ( ⟨ a, ha, ha' ⟩ | ⟨ a, b, c, d, hd, hd' ⟩ );
    · have := hcnm.granularN_injective ha'; aesop;
    · split_ifs at hd' <;> simp_all +decide ;
  · exact fun hp => Or.inl ⟨ p.1, hp, rfl ⟩

end PackageCalculus.Concurrent