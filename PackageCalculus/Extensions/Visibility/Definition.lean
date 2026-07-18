import PackageCalculus.Extensions.Concurrent.Definition

/-! # Visibility extension: definitions

Public/private dependencies. -/

namespace PackageCalculus.Visibility

open PackageCalculus

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]

/-- (p, n) ∈ pub means the dependency of package p on name n is public. -/
abbrev PubRel (N V : Type*) [DecidableEq N] [DecidableEq V] :=
  Finset (Package N V × N)

/-- p has a private dependency. -/
def Priv (Δ : DepRel N V) (pub : PubRel N V) (p : Package N V) : Prop :=
  ∃ n vs, (p, n, vs) ∈ Δ ∧ (p, n) ∉ pub

instance (Δ : DepRel N V) (pub : PubRel N V) (p : Package N V) :
    Decidable (Priv Δ pub p) :=
  decidable_of_iff (∃ e ∈ Δ, e.1 = p ∧ (p, e.2.1) ∉ pub) (by
    constructor
    · rintro ⟨⟨q, n, vs⟩, he, rfl, hnp⟩
      exact ⟨n, vs, he, hnp⟩
    · rintro ⟨n, vs, he, hnp⟩
      exact ⟨(p, n, vs), he, rfl, hnp⟩)

def IsOrigin (Δ : DepRel N V) (pub : PubRel N V) (r : Package N V)
    (S : Finset (Package N V)) (q : Package N V) : Prop :=
  q = r ∨ (q ∈ S ∧ Priv Δ pub q)

theorem IsOrigin.mem {Δ : DepRel N V} {pub : PubRel N V} {r q : Package N V}
    {S : Finset (Package N V)} (h : IsOrigin Δ pub r S q) (hr : r ∈ S) : q ∈ S := by
  rcases h with rfl | ⟨hq, _⟩
  · exact hr
  · exact hq

inductive InSub (pub : PubRel N V) (π : Finset (Package N V × Package N V))
    (q : Package N V) : Package N V → Prop
  | self : InSub pub π q q
  | child {c : Package N V} : (c, q) ∈ π → InSub pub π q c
  | pub_step {p : Package N V} {m : N} {u : V} :
      InSub pub π q p → ((m, u), p) ∈ π → (p, m) ∈ pub → InSub pub π q (m, u)

structure IsVisibilityResolution
    (R : Real N V) (Δ : DepRel N V) (pub : PubRel N V) (r : Package N V)
    (S : Finset (Package N V)) (π : Finset (Package N V × Package N V)) : Prop where
  concurrent : Concurrent.IsConcurrentResolution R Δ (id : V → V) r S π
  /-- No package sees two versions of a package name. -/
  version_visibility : ∀ p ∈ S, ∀ n : N, ∀ v v' : V,
    InSub pub π p (n, v) → InSub pub π p (n, v') → v = v'

end PackageCalculus.Visibility
