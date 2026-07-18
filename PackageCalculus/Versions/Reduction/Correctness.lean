import PackageCalculus.Versions.Reduction.Definition

namespace PackageCalculus

variable {N : Type*} [DecidableEq N] {V : Type*} [LT V] [DecidableEq V]
  [DecidableRel (· < · : V → V → Prop)]

theorem version_formula_correct (R : Real N V)
    (Δ_Φ : VFDepRel N V) (r : Package N V) (S : Finset (Package N V)) :
    IsResolution R (vfReduce R Δ_Φ) r S ↔ IsVFResolution R Δ_Φ r S := by
  constructor
  · rintro ⟨hsub, hroot, hdep, huniq⟩
    exact ⟨hsub, hroot,
      fun p hp m φ hφ =>
        hdep p hp m (φ.eval (repoVersions R m))
          (Finset.mem_image.mpr ⟨⟨p, m, φ⟩, hφ, rfl⟩),
      huniq⟩
  · rintro ⟨hsub, hroot, hdep, huniq⟩
    refine ⟨hsub, hroot, fun p hp m vs hmem => ?_, huniq⟩
    simp only [vfReduce, Finset.mem_image, Prod.mk.injEq] at hmem
    obtain ⟨⟨p', m', φ⟩, hφ, rfl, rfl, rfl⟩ := hmem
    exact hdep p' hp m' φ hφ

end PackageCalculus
