import PackageCalculus.Extensions.PackageFormula.Lifting.Definition

namespace PackageCalculus.PkgFormula

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hpn : HasPFNames N V N'] [hpv : Conflict.HasConflictVersions V V']

theorem liftResolution_completenessWitness
    (S_Ψ : Finset (Package N V)) (Δ_Ψ : PFDepRel N V) :
    liftResolution (completenessWitness S_Ψ Δ_Ψ) = S_Ψ := by
  ext p
  simp only [mem_liftResolution, completenessWitness, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion, embedPkg]
  constructor
  · intro h
    rcases h with ⟨q, hqS, heq⟩ | ⟨⟨q, ψ⟩, _, hw⟩
    · simp only [Prod.mk.injEq] at heq
      have h1 := hpn.origN.injective heq.1; have h2 := hpv.origV.injective heq.2
      exact (Prod.ext h1 h2 : q = p) ▸ hqS
    · -- hw : (origN p.1, origV p.2) ∈ if q ∈ S_Ψ then witnessSetTaken S_Ψ ψ else witnessSetUntaken S_Ψ ψ
      split at hw
      · exact absurd hw (witnessSetTaken_not_orig S_Ψ ψ p.1 _)
      · exact absurd hw (witnessSetUntaken_not_orig S_Ψ ψ p.1 _)
  · intro hp
    exact Or.inl ⟨p, hp, rfl⟩

theorem liftResolution_completeness
    (R_Ψ : Real N V) (Δ_Ψ : PFDepRel N V)
    (r : Package N V) (S_Ψ : Finset (Package N V))
    (hres : IsPFResolution R_Ψ Δ_Ψ r S_Ψ) :
    ∃ S', IsResolution (pfReal R_Ψ Δ_Ψ) (pfDeps Δ_Ψ) (embedPkg r) S' ∧
          liftResolution S' = S_Ψ :=
  ⟨completenessWitness S_Ψ Δ_Ψ,
   package_formula_completeness R_Ψ Δ_Ψ r S_Ψ hres,
   liftResolution_completenessWitness S_Ψ Δ_Ψ⟩


end PackageCalculus.PkgFormula
