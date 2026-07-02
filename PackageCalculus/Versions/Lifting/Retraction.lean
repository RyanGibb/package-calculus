import PackageCalculus.Versions.Lifting.Definition
import PackageCalculus.Versions.Reduction.Correctness

set_option linter.unusedSectionVars false

namespace PackageCalculus

variable {V : Type*} [DecidableEq V]
variable {N : Type*} [DecidableEq N]

/-! ## Round-trip theorem -/

/-- Reducing the lifted formulas gives back the original concrete deps.
    Requires every version set to be contained in the repository. -/
theorem liftVFDeps_vfReduce [LinearOrder V]
    (R : Real N V) (Δ : DepRel N V)
    (hsub : Δ.DependeesExist R) :
    vfReduce R (liftVFDeps R Δ) = Δ := by
  ext ⟨p, m, vs⟩
  simp only [vfReduce, liftVFDeps, Finset.mem_image]
  constructor
  · rintro ⟨⟨p', m', φ'⟩, ⟨⟨p'', m'', vs''⟩, hmem, hlift⟩, heq⟩
    have hsub' := hsub p'' m'' vs'' hmem
    simp only [Prod.mk.injEq] at hlift
    obtain ⟨rfl, rfl, rfl⟩ := hlift
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, hvs⟩ := heq
    have heval := finsetToFormula_eval (repoVersions R m'') vs'' hsub'
    rw [heval] at hvs
    rw [← hvs]; exact hmem
  · intro hmem
    have hsub' := hsub p m vs hmem
    refine ⟨(p, m, finsetToFormula (repoVersions R m) vs), ?_, ?_⟩
    · exact ⟨⟨p, m, vs⟩, hmem, rfl⟩
    · have heval := finsetToFormula_eval (repoVersions R m) vs hsub'
      rw [heval]

end PackageCalculus
