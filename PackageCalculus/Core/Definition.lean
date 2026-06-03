import Mathlib.Data.Finset.Basic

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

/-- S ∈ S(Δ, r): a resolution for dependencies Δ and root r within R. -/
structure IsResolution (R : Real N V) (Δ : DepRel N V)
    (r : Package N V) (S : Finset (Package N V)) : Prop where
  subset : S ⊆ R
  root_mem : r ∈ S
  dep_closure : ∀ p ∈ S, ∀ m : N, ∀ vs : Finset V,
    (p, m, vs) ∈ Δ → ∃ v ∈ vs, (m, v) ∈ S
  version_unique : VersionUnique S

end PackageCalculus
