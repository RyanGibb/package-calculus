import PackageCalculus.Core.Definition

/-! # SAT encoding of resolutions

A propositional predicate `σ` on packages satisfies a resolution problem
`(R, Δ, r)` iff it picks the root, is closed under dependencies, and selects
at most one version per name. Soundness and completeness of the encoding link
this predicate to `IsResolution`. -/

namespace PackageCalculus.Complexity

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]

/-- σ satisfies the SAT encoding of (R, Δ, r): root selected, dependency closure, at-most-one. -/
def satisfiesEncoding (R : Real N V) (Δ : DepRel N V)
    (r : Package N V) (σ : Package N V → Prop) : Prop :=
  σ r ∧
  (∀ p n vs, (p, n, vs) ∈ Δ → σ p → ∃ v ∈ vs, σ (n, v)) ∧
  (∀ n v v', (n, v) ∈ R → (n, v') ∈ R → v ≠ v' → ¬(σ (n, v) ∧ σ (n, v')))

omit [DecidableEq N] in
-- Paper Thm B.2 (SAT encoding soundness).
theorem satEncoding_soundness
    (R : Real N V) (Δ : DepRel N V) (r : Package N V)
    (σ : Package N V → Prop) [DecidablePred σ]
    (hr : r ∈ R)
    (hwf : ∀ p n vs, (p, n, vs) ∈ Δ → ∀ v ∈ vs, (n, v) ∈ R)
    (hsat : satisfiesEncoding R Δ r σ) :
    IsResolution R Δ r (R.filter (fun p => σ p)) := by
  obtain ⟨hroot, hdep, huniq⟩ := hsat
  exact {
    subset := fun _ hp => (Finset.mem_filter.mp hp).1
    root_mem := Finset.mem_filter.mpr ⟨hr, hroot⟩
    dep_closure := fun p hp m vs hd => by
      rw [Finset.mem_filter] at hp
      obtain ⟨_, hpσ⟩ := hp
      obtain ⟨v, hv, hvσ⟩ := hdep p m vs hd hpσ
      exact ⟨v, hv, Finset.mem_filter.mpr ⟨hwf p m vs hd v hv, hvσ⟩⟩
    version_unique := fun n v v' hv hv' => by
      rw [Finset.mem_filter] at hv hv'
      obtain ⟨hvR, hvσ⟩ := hv
      obtain ⟨hv'R, hv'σ⟩ := hv'
      by_contra h
      exact huniq n v v' hvR hv'R h ⟨hvσ, hv'σ⟩
  }

omit [DecidableEq N] [DecidableEq V] in
-- Paper Thm B.3 (SAT encoding completeness).
theorem satEncoding_completeness
    (R : Real N V) (Δ : DepRel N V) (r : Package N V)
    (S : Finset (Package N V))
    (hres : IsResolution R Δ r S) :
    satisfiesEncoding R Δ r (· ∈ S) := by
  refine ⟨hres.root_mem, fun p m vs hd hp => hres.dep_closure p hp m vs hd, ?_⟩
  intro n v v' _ _ hne ⟨hv, hv'⟩
  exact hne (hres.version_unique n v v' hv hv')

end PackageCalculus.Complexity
