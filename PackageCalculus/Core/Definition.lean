import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

/-! # Core dependency calculus

Defines the carriers of the calculus -- packages, the universe of available
packages (`Real`), and the dependency relation `DepRel` -- and what it means for
a finite set of packages to be a *resolution* for a dependency relation and root
package: a subset of the universe, closed under dependencies, with a unique
version per name. -/

namespace PackageCalculus

variable (N : Type*) [DecidableEq N] (V : Type*) [DecidableEq V]

abbrev Package := N × V

abbrev Real := Finset (Package N V)

/-- An element (p, m, vs) means package p depends on name m with compatible version set vs. -/
abbrev DepRel := Finset (Package N V × N × Finset V)

variable {N V}

def VersionUnique (S : Finset (Package N V)) : Prop :=
  ∀ n : N, ∀ v v' : V, (n, v) ∈ S → (n, v') ∈ S → v = v'

/-- A package depends on a given name with at most one compatible version set. -/
def DepRel.FunctionalInName (Δ : DepRel N V) : Prop :=
  ∀ p n vs₁ vs₂, (p, n, vs₁) ∈ Δ → (p, n, vs₂) ∈ Δ → vs₁ = vs₂

/-- The versions of name `m` available in `R`. -/
def repoVersions (R : Real N V) (m : N) : Finset V :=
  (R.filter (fun p => p.1 = m)).image Prod.snd

/-- S ∈ S(Δ, r): a resolution for dependencies Δ and root r within R. -/
structure IsResolution (R : Real N V) (Δ : DepRel N V)
    (r : Package N V) (S : Finset (Package N V)) : Prop where
  subset : S ⊆ R
  root_mem : r ∈ S
  dep_closure : ∀ p ∈ S, ∀ m : N, ∀ vs : Finset V,
    (p, m, vs) ∈ Δ → ∃ v ∈ vs, (m, v) ∈ S
  version_unique : VersionUnique S

/-- Restrict every version set in `Δ` to versions of real packages. -/
def DepRel.restrictReal (R : Real N V) (Δ : DepRel N V) : DepRel N V :=
  Δ.image (fun ⟨p, n, vs⟩ => (p, n, vs.filter (fun v => (n, v) ∈ R)))

/-- Restriction to real versions preserves the set of resolutions: a version
that is not real can never be selected, since `S ⊆ R`. -/
theorem restrictReal_resolution_iff (R : Real N V) (Δ : DepRel N V)
    (r : Package N V) (S : Finset (Package N V)) :
    IsResolution R (Δ.restrictReal R) r S ↔ IsResolution R Δ r S := by
  constructor
  · rintro ⟨hsub, hroot, hdep, huniq⟩
    refine ⟨hsub, hroot, fun p hp m vs hmem => ?_, huniq⟩
    obtain ⟨v, hv, hvS⟩ := hdep p hp m (vs.filter (fun v => (m, v) ∈ R))
      (Finset.mem_image.mpr ⟨⟨p, m, vs⟩, hmem, rfl⟩)
    exact ⟨v, (Finset.mem_filter.mp hv).1, hvS⟩
  · rintro ⟨hsub, hroot, hdep, huniq⟩
    refine ⟨hsub, hroot, fun p hp m vs hmem => ?_, huniq⟩
    simp only [DepRel.restrictReal, Finset.mem_image] at hmem
    obtain ⟨⟨p', m', vs'⟩, hmem', heq⟩ := hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    obtain ⟨v, hv, hvS⟩ := hdep p' hp m' vs' hmem'
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hsub hvS⟩, hvS⟩

end PackageCalculus
