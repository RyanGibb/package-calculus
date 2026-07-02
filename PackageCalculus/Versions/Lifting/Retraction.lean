import PackageCalculus.Versions.Lifting.Definition
import PackageCalculus.Versions.Reduction.Correctness

set_option linter.unusedSectionVars false

namespace PackageCalculus

variable {V : Type*} [DecidableEq V]
variable {N : Type*} [DecidableEq N]

/-! ## Round-trip theorem -/

/-- `v` is a version of `m` in `R` iff the package `(m, v)` is real. -/
private theorem mem_repoVersions {R : Real N V} {m : N} {v : V} :
    v ∈ repoVersions R m ↔ (m, v) ∈ R := by
  simp only [repoVersions, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hR, ha⟩, hb⟩
    dsimp only at ha hb
    subst ha; subst hb
    exact hR
  · exact fun h => ⟨(m, v), ⟨h, rfl⟩, rfl⟩

private theorem inter_repoVersions (R : Real N V) (m : N) (vs : Finset V) :
    vs ∩ repoVersions R m = vs.filter (fun v => (m, v) ∈ R) := by
  ext v
  simp only [Finset.mem_inter, Finset.mem_filter, mem_repoVersions]

/-- Reducing the lifted formulas gives back the original concrete deps,
    restricted to real versions. -/
theorem liftVFDeps_vfReduce [LinearOrder V]
    (R : Real N V) (Δ : DepRel N V) :
    vfReduce R (liftVFDeps R Δ) = Δ.restrictReal R := by
  unfold vfReduce liftVFDeps DepRel.restrictReal
  rw [Finset.image_image]
  refine Finset.image_congr fun x _ => ?_
  obtain ⟨p, m, vs⟩ := x
  simp only [Function.comp_apply]
  rw [finsetToFormula_eval, inter_repoVersions]

end PackageCalculus
