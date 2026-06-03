import PackageCalculus.Versions.Lifting.Definition
import PackageCalculus.Versions.Reduction.Correctness

set_option linter.unusedSectionVars false

namespace PackageCalculus

variable {V : Type*} [DecidableEq V]
variable {N : Type*} [DecidableEq N]

/-! ## Round-trip theorem -/

/-- Reducing the lifted formulas gives back the original concrete deps.
    Requires every version set to be nonempty and contained in the repository. -/
theorem liftVFDeps_vfReduce [LinearOrder V]
    (R : Real N V) (Δ : DepRel N V)
    (hne : ∀ p m vs, (p, m, vs) ∈ Δ → vs.Nonempty)
    (hsub : ∀ p m vs, (p, m, vs) ∈ Δ → vs ⊆ repoVersions R m) :
    vfReduce R (liftVFDeps R Δ) = Δ := by
  ext ⟨p, m, vs⟩
  simp only [vfReduce, liftVFDeps, Finset.mem_image]
  constructor
  · rintro ⟨⟨p', m', φ'⟩, ⟨⟨p'', m'', vs''⟩, hmem, hlift⟩, heq⟩
    have hne' := hne p'' m'' vs'' hmem
    have hsub' := hsub p'' m'' vs'' hmem
    simp only [dif_pos hne', Prod.mk.injEq] at hlift
    obtain ⟨rfl, rfl, rfl⟩ := hlift
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, hvs⟩ := heq
    have heval := finsetToFormula_eval (repoVersions R m'') vs'' hne' hsub'
    rw [heval] at hvs
    rw [← hvs]; exact hmem
  · intro hmem
    have hne' := hne p m vs hmem
    have hsub' := hsub p m vs hmem
    refine ⟨(p, m, finsetToFormula (repoVersions R m) vs hne'), ?_, ?_⟩
    · exact ⟨⟨p, m, vs⟩, hmem, by simp [dif_pos hne']⟩
    · have heval := finsetToFormula_eval (repoVersions R m) vs hne' hsub'
      rw [heval]

end PackageCalculus
