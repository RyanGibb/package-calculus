import PackageCalculus.Extensions.PackageFormula.Lifting.Definition

namespace PackageCalculus.PkgFormula

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hpn : HasPFNames N V N'] [hpv : Conflict.HasConflictVersions V V']

/-! ## Round-trip theorems -/

theorem liftReal_pfReal (R : Real N V) (Δ_Ψ : PFDepRel N V) :
    liftReal (pfReal R Δ_Ψ) = R := by
  ext p
  simp only [mem_liftReal, pfReal, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion]
  constructor
  · intro h
    rcases h with ⟨q, hqR, heq⟩ | ⟨a, haΔ, hmem⟩
    · simp only [embedPkg, Prod.mk.injEq] at heq
      have h1 := hpn.origN.injective heq.1; have h2 := hpv.origV.injective heq.2
      exact (Prod.ext h1 h2 : q = p) ▸ hqR
    · exfalso
      exact witnessPackages_not_orig (embedPkg a.1) a.2 p.1 (hpv.origV p.2) hmem
  · intro hp
    exact Or.inl ⟨p, hp, rfl⟩


end PackageCalculus.PkgFormula
