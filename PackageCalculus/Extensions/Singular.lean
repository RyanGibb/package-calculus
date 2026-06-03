import PackageCalculus.Core.Definition
import Mathlib.Data.Finset.Image

/-! # Singular dependencies

Dependencies pinned to a single `(package, required-package)` pair, together
with `IsSingularResolution` and a reduction to the core calculus. -/

namespace PackageCalculus.Singular

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]

/-- Singular dependency relation: (package, required-package). -/
abbrev SingularRel (N V : Type*) [DecidableEq N] [DecidableEq V] :=
  Finset (Package N V × Package N V)

structure IsSingularResolution
    (R : Real N V) (beta : SingularRel N V)
    (r : Package N V) (S : Finset (Package N V)) : Prop where
  subset : S ⊆ R
  root_mem : r ∈ S
  dep_closure : ∀ p ∈ S, ∀ d, (p, d) ∈ beta → d ∈ S
  version_unique : VersionUnique S

def singularToCore (beta : SingularRel N V) : DepRel N V :=
  beta.image fun ⟨p, q⟩ => (p, q.1, ({q.2} : Finset V))

theorem singular_is_core (R : Real N V) (beta : SingularRel N V)
    (r : Package N V) (S : Finset (Package N V)) :
    IsSingularResolution R beta r S → IsResolution R (singularToCore beta) r S := by
  intro ⟨hsub, hroot, hdep, huniq⟩
  refine ⟨hsub, hroot, fun p hp m vs hmem => ?_, huniq⟩
  simp only [singularToCore, Finset.mem_image] at hmem
  obtain ⟨⟨p', n, v⟩, hbeta, heq⟩ := hmem
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨v, Finset.mem_singleton.mpr rfl, hdep _ hp (n, v) hbeta⟩

end PackageCalculus.Singular
