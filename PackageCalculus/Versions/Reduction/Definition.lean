import PackageCalculus.Versions.Formula

/-! # Reducing version-formula resolutions to base resolutions

`vfReduce` evaluates every `VersionFormula` in a `VFDepRel` against the
available versions in `R`, producing a plain `DepRel`. -/

namespace PackageCalculus

variable {N : Type*} [DecidableEq N] {V : Type*} [LT V] [DecidableEq V]
  [DecidableRel (· < · : V → V → Prop)]

def vfReduce (R : Real N V) (Δ_Φ : VFDepRel N V) : DepRel N V :=
  Δ_Φ.image (fun ⟨p, m, φ⟩ => (p, m, φ.eval (repoVersions R m)))

end PackageCalculus
