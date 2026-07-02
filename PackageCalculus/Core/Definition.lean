import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union

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

/-- The intersection of every version set `Δ` assigns to `(p, n)`. -/
def DepRel.mergedVS (Δ : DepRel N V) (p : Package N V) (n : N) : Finset V :=
  (Δ.biUnion (fun e => if e.1 = p ∧ e.2.1 = n then e.2.2 else ∅)).filter
    (fun v => ∀ e ∈ Δ, e.1 = p → e.2.1 = n → v ∈ e.2.2)

theorem DepRel.mem_mergedVS {Δ : DepRel N V} {p : Package N V} {n : N} {v : V} :
    v ∈ Δ.mergedVS p n ↔
      (∃ vs, (p, n, vs) ∈ Δ) ∧ ∀ vs, (p, n, vs) ∈ Δ → v ∈ vs := by
  simp only [mergedVS, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨e, he, hv⟩, hall⟩
    split at hv
    case isTrue h =>
      refine ⟨⟨e.2.2, ?_⟩, fun vs hvs => hall (p, n, vs) hvs rfl rfl⟩
      rw [← h.1, ← h.2]
      exact he
    case isFalse => exact absurd hv (Finset.notMem_empty v)
  · rintro ⟨⟨vs₀, h₀⟩, hall⟩
    refine ⟨⟨(p, n, vs₀), h₀, by rw [if_pos ⟨rfl, rfl⟩]; exact hall vs₀ h₀⟩,
      fun e he h1 h2 => ?_⟩
    obtain ⟨q, m, vs⟩ := e
    dsimp only at h1 h2 ⊢
    subst h1; subst h2
    exact hall vs he

/-- Merge same-name entries per depender by intersecting their version sets. -/
def DepRel.merge (Δ : DepRel N V) : DepRel N V :=
  (Δ.image (fun e => (e.1, e.2.1))).image (fun q => (q.1, q.2, Δ.mergedVS q.1 q.2))

theorem DepRel.mem_merge {Δ : DepRel N V} {p : Package N V} {n : N} {vs : Finset V} :
    (p, n, vs) ∈ Δ.merge ↔ (∃ vs₀, (p, n, vs₀) ∈ Δ) ∧ vs = Δ.mergedVS p n := by
  simp only [merge, Finset.mem_image]
  constructor
  · rintro ⟨q, ⟨e, he, rfl⟩, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2, h3⟩ := heq
    subst h1; subst h2
    exact ⟨⟨e.2.2, he⟩, h3.symm⟩
  · rintro ⟨⟨vs₀, h₀⟩, rfl⟩
    exact ⟨(p, n), ⟨(p, n, vs₀), h₀, rfl⟩, rfl⟩

theorem DepRel.merge_functionalInName (Δ : DepRel N V) : Δ.merge.FunctionalInName := by
  intro p n vs₁ vs₂ h₁ h₂
  rw [DepRel.mem_merge] at h₁ h₂
  rw [h₁.2, h₂.2]

/-- Merging preserves the set of resolutions: version uniqueness already forces
every same-name entry to be satisfied by the one selected version. -/
theorem merge_resolution_iff (R : Real N V) (Δ : DepRel N V)
    (r : Package N V) (S : Finset (Package N V)) :
    IsResolution R Δ.merge r S ↔ IsResolution R Δ r S := by
  constructor
  · rintro ⟨hsub, hroot, hdep, huniq⟩
    refine ⟨hsub, hroot, fun p hp m vs hmem => ?_, huniq⟩
    obtain ⟨v, hv, hvS⟩ := hdep p hp m (Δ.mergedVS p m)
      (DepRel.mem_merge.mpr ⟨⟨vs, hmem⟩, rfl⟩)
    exact ⟨v, (DepRel.mem_mergedVS.mp hv).2 vs hmem, hvS⟩
  · rintro ⟨hsub, hroot, hdep, huniq⟩
    refine ⟨hsub, hroot, fun p hp m vs hmem => ?_, huniq⟩
    rw [DepRel.mem_merge] at hmem
    obtain ⟨⟨vs₀, h₀⟩, rfl⟩ := hmem
    obtain ⟨v₀, hv₀, hv₀S⟩ := hdep p hp m vs₀ h₀
    refine ⟨v₀, DepRel.mem_mergedVS.mpr ⟨⟨vs₀, h₀⟩, fun vs' h' => ?_⟩, hv₀S⟩
    obtain ⟨v', hv', hv'S⟩ := hdep p hp m vs' h'
    rwa [huniq m v₀ v' hv₀S hv'S]

end PackageCalculus
