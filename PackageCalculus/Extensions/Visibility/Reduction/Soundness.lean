import PackageCalculus.Extensions.Visibility.Reduction.Definition

/-! # Visibility extension: soundness -/

namespace PackageCalculus.Visibility

open Classical PackageCalculus

set_option linter.unusedSectionVars false

variable {N : Type*} {V : Type*} {N' : Type*}
variable [DecidableEq N] [DecidableEq V] [DecidableEq N']
variable [hvn : HasVisibilityNames N V N']

/-- The extracted resolution: real packages some occurrence of which is selected. -/
def soundnessS (R_C : Real N V) (Δ : DepRel N V) (pub : PubRel N V)
    (r : Package N V) (S : Finset (Package N' V)) : Finset (Package N V) :=
  R_C.filter fun p => ∃ q ∈ potentialOrigins R_C Δ pub r, (hvn.occurrenceN p.1 q, p.2) ∈ S

theorem mem_soundnessS {R_C : Real N V} {Δ : DepRel N V} {pub : PubRel N V}
    {r : Package N V} {S : Finset (Package N' V)} {p : Package N V} :
    p ∈ soundnessS R_C Δ pub r S ↔
      p ∈ R_C ∧ ∃ q ∈ potentialOrigins R_C Δ pub r, (hvn.occurrenceN p.1 q, p.2) ∈ S := by
  simp [soundnessS]

theorem occurrence_mem_soundnessS {R_C : Real N V} {Δ : DepRel N V} {pub : PubRel N V}
    {r : Package N V} {S : Finset (Package N' V)}
    {n : N} {q : Package N V} {v : V}
    (hsub : S ⊆ visReal R_C Δ pub r)
    (h : (hvn.occurrenceN n q, v) ∈ S) : (n, v) ∈ soundnessS R_C Δ pub r S := by
  obtain ⟨hR, hq⟩ := occurrence_mem_visReal_elim (hsub h)
  exact mem_soundnessS.mpr ⟨hR, q, hq, h⟩

/-- The extracted parent relation, from the agreements. -/
def soundnessπ (R_C : Real N V) (Δ : DepRel N V) (pub : PubRel N V)
    (r : Package N V) (S : Finset (Package N' V)) :
    Finset (Package N V × Package N V) :=
  Δ.biUnion fun ⟨⟨n, v⟩, m, vs⟩ =>
    (vs.filter fun u => (hvn.agreementN n v m, u) ∈ S ∧
        (n, v) ∈ soundnessS R_C Δ pub r S).image
      fun u => ((m, u), (n, v))

theorem mem_soundnessπ {R_C : Real N V} {Δ : DepRel N V} {pub : PubRel N V}
    {r : Package N V} {S : Finset (Package N' V)}
    {pair : Package N V × Package N V} :
    pair ∈ soundnessπ R_C Δ pub r S ↔
      ∃ n v m vs u, ((n, v), m, vs) ∈ Δ ∧ u ∈ vs ∧
        (hvn.agreementN n v m, u) ∈ S ∧
        (n, v) ∈ soundnessS R_C Δ pub r S ∧
        pair = ((m, u), (n, v)) := by
  simp only [soundnessπ, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨⟨n, v⟩, m, vs⟩, hdep, u, ⟨hu, hagr, hnv⟩, rfl⟩
    exact ⟨n, v, m, vs, u, hdep, hu, hagr, hnv, rfl⟩
  · rintro ⟨n, v, m, vs, u, hdep, hu, hagr, hnv, rfl⟩
    exact ⟨⟨⟨n, v⟩, m, vs⟩, hdep, u, ⟨hu, hagr, hnv⟩, rfl⟩

/-- A selected occurrence's carried edge selects the dependee's occurrence at the same origin. -/
theorem occurrence_step {R_C : Real N V} {Δ : DepRel N V} {pub : PubRel N V}
    {r : Package N V} {S : Finset (Package N' V)}
    {n : N} {v : V} {m : N} {vs : Finset V} {q : Package N V}
    (hres : IsResolution (visReal R_C Δ pub r) (visDeps R_C Δ pub r) (visRoot r) S)
    (hdep : ((n, v), m, vs) ∈ Δ) (hq : q ∈ potentialOrigins R_C Δ pub r)
    (he : carried pub (n, v) m q)
    (hocc : (hvn.occurrenceN n q, v) ∈ S) :
    ∃ u ∈ vs, (hvn.intermediateN n v m q, u) ∈ S ∧
      (hvn.agreementN n v m, u) ∈ S ∧ (hvn.occurrenceN m q, u) ∈ S := by
  obtain ⟨u, hu, hintS⟩ := hres.dep_closure _ hocc _ _ (mem_visDeps_occ2int hdep hq he)
  obtain ⟨w₁, hw₁, hagrS⟩ := hres.dep_closure _ hintS _ _ (mem_visDeps_int2agr hdep hq he hu)
  rw [Finset.mem_singleton] at hw₁; rw [hw₁] at hagrS
  obtain ⟨w₂, hw₂, hcpS⟩ := hres.dep_closure _ hintS _ _ (mem_visDeps_int2occ hdep hq he hu)
  rw [Finset.mem_singleton] at hw₂; rw [hw₂] at hcpS
  exact ⟨u, hu, hintS, hagrS, hcpS⟩

theorem occurrence_step_at {R_C : Real N V} {Δ : DepRel N V} {pub : PubRel N V}
    {r : Package N V} {S : Finset (Package N' V)}
    {n : N} {v : V} {m : N} {vs : Finset V} {q : Package N V} {u : V}
    (hres : IsResolution (visReal R_C Δ pub r) (visDeps R_C Δ pub r) (visRoot r) S)
    (hdep : ((n, v), m, vs) ∈ Δ) (hq : q ∈ potentialOrigins R_C Δ pub r)
    (he : carried pub (n, v) m q)
    (hocc : (hvn.occurrenceN n q, v) ∈ S)
    (hagr : (hvn.agreementN n v m, u) ∈ S) :
    u ∈ vs ∧ (hvn.occurrenceN m q, u) ∈ S := by
  obtain ⟨u', hu', _, hagr', hcp'⟩ := occurrence_step hres hdep hq he hocc
  have heq : u' = u := hres.version_unique _ _ _ hagr' hagr
  subst heq
  exact ⟨hu', hcp'⟩

/-- A private-depender's own occurrence is selected whenever any of its occurrences is. -/
theorem self_occurrence {R_C : Real N V} {Δ : DepRel N V} {pub : PubRel N V}
    {r : Package N V} {S : Finset (Package N' V)}
    {p q : Package N V}
    (hres : IsResolution (visReal R_C Δ pub r) (visDeps R_C Δ pub r) (visRoot r) S)
    (hpR : p ∈ R_C) (hq : q ∈ potentialOrigins R_C Δ pub r)
    (hpriv : Priv Δ pub p)
    (hocc : (hvn.occurrenceN p.1 q, p.2) ∈ S) :
    (hvn.occurrenceN p.1 p, p.2) ∈ S := by
  by_cases hqp : q = p
  · exact hqp ▸ hocc
  · obtain ⟨w, hw, hself⟩ :=
      hres.dep_closure _ hocc _ _ (mem_visDeps_self hpR hq hpriv hqp)
    rw [Finset.mem_singleton] at hw
    rw [hw] at hself
    exact hself

/-- Every selected package has a selected occurrence at an origin carrying all its edges. -/
theorem base_occurrence {R_C : Real N V} {Δ : DepRel N V} {pub : PubRel N V}
    {r : Package N V} {S : Finset (Package N' V)} {p : Package N V}
    (hres : IsResolution (visReal R_C Δ pub r) (visDeps R_C Δ pub r) (visRoot r) S)
    (hp : p ∈ soundnessS R_C Δ pub r S) :
    ∃ c₀ ∈ potentialOrigins R_C Δ pub r, (hvn.occurrenceN p.1 c₀, p.2) ∈ S ∧
      ∀ m vs, (p, m, vs) ∈ Δ → carried pub p m c₀ := by
  obtain ⟨hR, q, hq, hocc⟩ := mem_soundnessS.mp hp
  by_cases hpriv : Priv Δ pub p
  · exact ⟨p, mem_potentialOrigins.mpr (Or.inr ⟨hR, hpriv⟩),
      self_occurrence hres hR hq hpriv hocc, fun m vs _ => Or.inr rfl⟩
  · refine ⟨q, hq, hocc, ?_⟩
    intro m vs hdep
    left
    by_contra h
    exact hpriv ⟨m, vs, hdep, h⟩

/-- Subgraph members have selected occurrences at the common origin. -/
theorem inSub_occurrence {R_C : Real N V} {Δ : DepRel N V} {pub : PubRel N V}
    {r : Package N V} {S : Finset (Package N' V)}
    {p c c₀ : Package N V}
    (hres : IsResolution (visReal R_C Δ pub r) (visDeps R_C Δ pub r) (visRoot r) S)
    (hc₀ : c₀ ∈ potentialOrigins R_C Δ pub r)
    (hoccp : (hvn.occurrenceN p.1 c₀, p.2) ∈ S)
    (htr : ∀ m vs, (p, m, vs) ∈ Δ → carried pub p m c₀)
    (hc : InSub pub (soundnessπ R_C Δ pub r S) p c) :
    (hvn.occurrenceN c.1 c₀, c.2) ∈ S := by
  induction hc with
  | self => exact hoccp
  | child hedge =>
    rw [mem_soundnessπ] at hedge
    obtain ⟨n, v, m, vs, u, hdep, hu, hagr, hnv, heq⟩ := hedge
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact (occurrence_step_at hres hdep hc₀ (htr m vs hdep) hoccp hagr).2
  | pub_step hins hedge hpub ih =>
    rw [mem_soundnessπ] at hedge
    obtain ⟨n, v, m', vs, u', hdep, hu, hagr, hnv, heq⟩ := hedge
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    exact (occurrence_step_at hres hdep hc₀ (Or.inl hpub) ih hagr).2

theorem visibility_soundness
    (R_C : Real N V) (Δ_C : DepRel N V) (pub : PubRel N V) (r : Package N V)
    (S : Finset (Package N' V))
    (hres : IsResolution (visReal R_C Δ_C pub r) (visDeps R_C Δ_C pub r)
      (visRoot r) S) :
    IsVisibilityResolution R_C Δ_C pub r
      (soundnessS R_C Δ_C pub r S) (soundnessπ R_C Δ_C pub r S) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- subset
    intro p hp
    exact (mem_soundnessS.mp hp).1
  · -- root_mem
    exact occurrence_mem_soundnessS hres.subset hres.root_mem
  · -- parent_closure
    intro p hp m vs hdep
    obtain ⟨pn, pv⟩ := p
    obtain ⟨c₀, hc₀, hocc, htr⟩ := base_occurrence hres hp
    obtain ⟨u, hu, hint, hagr, hcpS⟩ :=
      occurrence_step hres hdep hc₀ (htr m vs hdep) hocc
    have hmu : (m, u) ∈ soundnessS R_C Δ_C pub r S :=
      occurrence_mem_soundnessS hres.subset hcpS
    refine ⟨u, ⟨hu, hmu, ?_⟩, ?_⟩
    · rw [mem_soundnessπ]
      exact ⟨pn, pv, m, vs, u, hdep, hu, hagr, hp, rfl⟩
    · rintro u' ⟨hu', hmu', hπ'⟩
      rw [mem_soundnessπ] at hπ'
      obtain ⟨n₂, v₂, m₂, vs₂, u₂, hdep₂, hu₂, hagr₂, _, heq⟩ := hπ'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
      exact hres.version_unique _ _ _ hagr₂ hagr
  · -- version_granularity (identity granularity: vacuous)
    intro n v v' _ _ hne
    exact hne
  · -- parent_subset
    intro c p hcp
    rw [mem_soundnessπ] at hcp
    obtain ⟨n, v, m, vs, u, hdep, hu, hagr, hnv, heq⟩ := hcp
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨c₀, hc₀, hocc, htr⟩ := base_occurrence hres hnv
    exact ⟨occurrence_mem_soundnessS hres.subset
      (occurrence_step_at hres hdep hc₀ (htr m vs hdep) hocc hagr).2, hnv⟩
  · -- version_visibility
    intro p hp n v v' hv hv'
    obtain ⟨c₀, hc₀, hocc, htr⟩ := base_occurrence hres hp
    exact hres.version_unique _ _ _
      (inSub_occurrence hres hc₀ hocc htr hv) (inSub_occurrence hres hc₀ hocc htr hv')

end PackageCalculus.Visibility
