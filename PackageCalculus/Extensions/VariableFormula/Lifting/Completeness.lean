import PackageCalculus.Extensions.VariableFormula.Lifting.Definition

namespace PackageCalculus.VarFormula

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {X : Type*} [DecidableEq X] {Y : Type*} [DecidableEq Y]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVFNames N V X Y N'] [hvv : HasVFVersions V Y V']

theorem liftResolution_completenessWitness
    [LT Y] [DecidableRel (· < · : Y → Y → Prop)] [Fintype X]
    (S_Ψ : Finset (Package N V)) (Δ_Ψ : VFDepRel N V X Y)
    (σ : X → Y) :
    liftResolution (X := X) (Y := Y)
      (completenessWitness (N' := N') (V' := V') S_Ψ Δ_Ψ σ) = S_Ψ := by
  apply Finset.ext;
  intro p
  simp [mem_liftResolution, completenessWitness];
  constructor <;> intro h
  all_goals generalize_proofs at *;
  · rcases h with ( ⟨ a, b, h, h' ⟩ | ⟨ a, b, c, h, h' ⟩ | ⟨ a, h ⟩ ) <;> simp_all +decide [ embedPkg ];
    split_ifs at h' <;> [ exact False.elim ( witnessSetTaken_not_orig _ _ _ _ _ h' ) ; exact False.elim ( witnessSetUntaken_not_orig _ _ _ _ h' ) ];
  · exact Or.inl ⟨ p.1, p.2, h, rfl ⟩

theorem liftResolution_completeness
    [LT Y] [DecidableRel (· < · : Y → Y → Prop)] [Fintype X]
    (Y_x : X → Finset Y)
    (R_Ψ : Real N V) (Δ_Ψ : VFDepRel N V X Y)
    (r : Package N V) (σ : X → Y)
    (hσ_dom : ∀ x, σ x ∈ Y_x x)
    (S_Ψ : Finset (Package N V))
    (hres : IsVFResolution R_Ψ Δ_Ψ r S_Ψ σ) :
    ∃ S', IsResolution (vfReal (N' := N') (V' := V') Y_x R_Ψ Δ_Ψ)
        (vfDeps (N' := N') (V' := V') Y_x Δ_Ψ)
        (embedPkg (X := X) (Y := Y) r) S' ∧
      liftResolution (X := X) (Y := Y) S' = S_Ψ :=
  ⟨completenessWitness (N' := N') (V' := V') S_Ψ Δ_Ψ σ,
   varFormula_completeness Y_x R_Ψ Δ_Ψ r σ hσ_dom S_Ψ hres,
   liftResolution_completenessWitness S_Ψ Δ_Ψ σ⟩


end PackageCalculus.VarFormula
