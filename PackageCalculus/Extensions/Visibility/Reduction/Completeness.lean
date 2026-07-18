import PackageCalculus.Extensions.Visibility.Reduction.Definition
import Mathlib.Data.Finset.Prod

/-! # Visibility extension: completeness -/

namespace PackageCalculus.Visibility

open Classical PackageCalculus

set_option linter.unusedSectionVars false

variable {N : Type*} {V : Type*} {N' : Type*}
variable [DecidableEq N] [DecidableEq V] [DecidableEq N']
variable [hvn : HasVisibilityNames N V N']

noncomputable def completenessWitness (R_C : Real N V) (Δ : DepRel N V)
    (pub : PubRel N V) (r : Package N V) (S_pub : Finset (Package N V))
    (π : Finset (Package N V × Package N V)) : Finset (Package N' V) :=
  -- Occurrences: q an origin of the resolution, the package in its subgraph
  (((S_pub ×ˢ potentialOrigins R_C Δ pub r).filter fun x =>
      IsOrigin Δ pub r S_pub x.2 ∧ InSub pub π x.2 x.1).image
    fun x => (hvn.occurrenceN x.1.1 x.2, x.1.2)) ∪
  -- Intermediates: at materialised edges, carrying the parent-selected version
  (Δ.biUnion fun ⟨⟨n, v⟩, m, vs⟩ => (potentialOrigins R_C Δ pub r).biUnion fun q =>
    (vs.filter fun u => IsOrigin Δ pub r S_pub q ∧ InSub pub π q (n, v) ∧
        carried pub (n, v) m q ∧ ((m, u), (n, v)) ∈ π).image
      fun u => (hvn.intermediateN n v m q, u)) ∪
  -- Agreements: per parent edge
  (Δ.biUnion fun ⟨⟨n, v⟩, m, vs⟩ =>
    (vs.filter fun u => (n, v) ∈ S_pub ∧ ((m, u), (n, v)) ∈ π).image
      fun u => (hvn.agreementN n v m, u))

section Witness

variable {R_C : Real N V} {Δ : DepRel N V} {pub : PubRel N V} {r : Package N V}
variable {S_pub : Finset (Package N V)}
variable {π : Finset (Package N V × Package N V)}

theorem mem_witness_occurrence {p q : Package N V}
    (hpS : p ∈ S_pub) (hq : q ∈ potentialOrigins R_C Δ pub r)
    (horigin : IsOrigin Δ pub r S_pub q) (hins : InSub pub π q p) :
    (hvn.occurrenceN p.1 q, p.2) ∈ completenessWitness R_C Δ pub r S_pub π := by
  simp only [completenessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_product]
  exact Or.inl (Or.inl ⟨(p, q), ⟨⟨hpS, hq⟩, horigin, hins⟩, rfl⟩)

theorem mem_witness_intermediate {n : N} {v : V} {m : N} {vs : Finset V}
    {q : Package N V} {u : V}
    (hdep : ((n, v), m, vs) ∈ Δ) (hq : q ∈ potentialOrigins R_C Δ pub r) (hu : u ∈ vs)
    (horigin : IsOrigin Δ pub r S_pub q) (hins : InSub pub π q (n, v))
    (he : carried pub (n, v) m q) (hedge : ((m, u), (n, v)) ∈ π) :
    (hvn.intermediateN n v m q, u) ∈ completenessWitness R_C Δ pub r S_pub π := by
  simp only [completenessWitness, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter]
  exact Or.inl (Or.inr ⟨⟨(n, v), m, vs⟩, hdep, q, hq, u, ⟨hu, horigin, hins, he, hedge⟩, rfl⟩)

theorem mem_witness_agreement {n : N} {v : V} {m : N} {vs : Finset V} {u : V}
    (hdep : ((n, v), m, vs) ∈ Δ) (hu : u ∈ vs)
    (hnv : (n, v) ∈ S_pub) (hedge : ((m, u), (n, v)) ∈ π) :
    (hvn.agreementN n v m, u) ∈ completenessWitness R_C Δ pub r S_pub π := by
  simp only [completenessWitness, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter]
  exact Or.inr ⟨⟨(n, v), m, vs⟩, hdep, u, ⟨hu, hnv, hedge⟩, rfl⟩

theorem witness_mem_cases {pkg : Package N' V}
    (h : pkg ∈ completenessWitness R_C Δ pub r S_pub π) :
    (∃ n v q, (n, v) ∈ S_pub ∧ q ∈ potentialOrigins R_C Δ pub r ∧
      IsOrigin Δ pub r S_pub q ∧ InSub pub π q (n, v) ∧
      pkg = (hvn.occurrenceN n q, v)) ∨
    (∃ n v m vs q u, ((n, v), m, vs) ∈ Δ ∧ q ∈ potentialOrigins R_C Δ pub r ∧
      u ∈ vs ∧ IsOrigin Δ pub r S_pub q ∧ InSub pub π q (n, v) ∧
      carried pub (n, v) m q ∧ ((m, u), (n, v)) ∈ π ∧
      pkg = (hvn.intermediateN n v m q, u)) ∨
    (∃ n v m vs u, ((n, v), m, vs) ∈ Δ ∧ u ∈ vs ∧ (n, v) ∈ S_pub ∧
      ((m, u), (n, v)) ∈ π ∧ pkg = (hvn.agreementN n v m, u)) := by
  simp only [completenessWitness, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter, Finset.mem_product] at h
  rcases h with (⟨⟨p, q⟩, ⟨⟨hpS, hq⟩, horigin, hins⟩, rfl⟩ |
      ⟨⟨⟨n, v⟩, m, vs⟩, hdep, q, hq, u, ⟨hu, horigin, hins, he, hedge⟩, rfl⟩) |
    ⟨⟨⟨n, v⟩, m, vs⟩, hdep, u, ⟨hu, hnv, hedge⟩, rfl⟩
  · exact Or.inl ⟨p.1, p.2, q, hpS, hq, horigin, hins, rfl⟩
  · exact Or.inr (Or.inl ⟨n, v, m, vs, q, u, hdep, hq, hu, horigin, hins, he, hedge, rfl⟩)
  · exact Or.inr (Or.inr ⟨n, v, m, vs, u, hdep, hu, hnv, hedge, rfl⟩)

end Witness

theorem visibility_completeness
    (R_C : Real N V) (Δ_C : DepRel N V) (pub : PubRel N V) (r : Package N V)
    (S_pub : Finset (Package N V)) (π : Finset (Package N V × Package N V))
    (hfn : Δ_C.FunctionalInName)
    (hres : IsVisibilityResolution R_C Δ_C pub r S_pub π) :
    IsResolution (visReal R_C Δ_C pub r) (visDeps R_C Δ_C pub r) (visRoot r)
      (completenessWitness R_C Δ_C pub r S_pub π (N' := N')) := by
  have hπsub := hres.concurrent.parent_subset
  have hrS := hres.concurrent.root_mem
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- subset
    intro pkg h
    rcases witness_mem_cases h with
      ⟨n, v, q, hpS, hq, _, _, rfl⟩ |
      ⟨n, v, m, vs, q, u, hdep, hq, hu, _, _, _, _, rfl⟩ |
      ⟨n, v, m, vs, u, hdep, hu, _, _, rfl⟩
    · exact occurrence_mem_visReal (hres.concurrent.subset hpS) hq
    · exact intermediate_mem_visReal hdep hq hu
    · exact agreement_mem_visReal hdep hu
  · -- root_mem
    exact mem_witness_occurrence hrS
      (mem_potentialOrigins.mpr (Or.inl rfl)) (Or.inl rfl) InSub.self
  · -- dep_closure
    intro pkg hpkg tn tvs hdep'
    rw [mem_visDeps_iff] at hdep'
    rcases witness_mem_cases hpkg with
      ⟨n, v, q, hpS, hq, horigin, hins, rfl⟩ |
      ⟨n, v, m, vs, q, u, hdep, hq, hu, horigin, hins, he, hedge, rfl⟩ |
      ⟨n, v, m, vs, u, hdep, hu, hnv, hedge, rfl⟩
    · -- source is a occurrence: self-edge or occurrence→intermediate
      rcases hdep' with ⟨p₁, q₁, hp₁, hq₁, hpriv₁, hne₁, heq⟩ |
          ⟨n₁, v₁, m₁, vs₁, q₁, hdep₁, hq₁, he₁, heq⟩ |
          ⟨n₁, v₁, m₁, vs₁, q₁, u₁, _, _, _, _, heq⟩ |
          ⟨n₁, v₁, m₁, vs₁, q₁, u₁, _, _, _, _, heq⟩
      · -- self-edge
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := heq
        obtain ⟨rfl, rfl⟩ := hvn.occurrenceN_injective _ _ _ _ h1
        subst h2 h3 h4
        refine ⟨p₁.2, Finset.mem_singleton_self _, ?_⟩
        exact mem_witness_occurrence hpS
          (mem_potentialOrigins.mpr (Or.inr ⟨hp₁, hpriv₁⟩))
          (Or.inr ⟨hpS, hpriv₁⟩) InSub.self
      · -- occurrence→intermediate: use the parent-selected version
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := heq
        obtain ⟨rfl, rfl⟩ := hvn.occurrenceN_injective _ _ _ _ h1
        subst h2 h3 h4
        obtain ⟨u₂, ⟨hu₂, hmS₂, hedge₂⟩, -⟩ :=
          hres.concurrent.parent_closure _ hpS _ _ hdep₁
        refine ⟨u₂, hu₂, ?_⟩
        exact mem_witness_intermediate hdep₁ hq hu₂ horigin hins he₁ hedge₂
      · simp only [Prod.mk.injEq] at heq
        exact absurd heq.1.1 (hvn.occurrenceN_ne_intermediateN _ _ _ _ _ _)
      · simp only [Prod.mk.injEq] at heq
        exact absurd heq.1.1 (hvn.occurrenceN_ne_intermediateN _ _ _ _ _ _)
    · -- source is an intermediate: dependee occurrence or agreement
      rcases hdep' with ⟨p₁, q₁, _, _, _, _, heq⟩ |
          ⟨n₁, v₁, m₁, vs₁, q₁, _, _, _, heq⟩ |
          ⟨n₁, v₁, m₁, vs₁, q₁, u₁, hdep₁, hq₁, he₁, hu₁, heq⟩ |
          ⟨n₁, v₁, m₁, vs₁, q₁, u₁, hdep₁, hq₁, he₁, hu₁, heq⟩
      · simp only [Prod.mk.injEq] at heq
        exact absurd heq.1.1 (hvn.intermediateN_ne_occurrenceN _ _ _ _ _ _)
      · simp only [Prod.mk.injEq] at heq
        exact absurd heq.1.1.symm (hvn.occurrenceN_ne_intermediateN _ _ _ _ _ _)
      · -- intermediate → dependee occurrence at the same origin
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := heq
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hvn.intermediateN_injective _ _ _ _ _ _ _ _ h1
        subst h2 h3 h4
        refine ⟨u, Finset.mem_singleton_self _, ?_⟩
        have hmS : (m, u) ∈ S_pub := (hπsub _ _ hedge).1
        have hins' : InSub pub π q (m, u) := by
          rcases he with hpub | rfl
          · exact InSub.pub_step hins hedge hpub
          · exact InSub.child hedge
        exact mem_witness_occurrence hmS hq horigin hins'
      · -- intermediate → agreement
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := heq
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hvn.intermediateN_injective _ _ _ _ _ _ _ _ h1
        subst h2 h3 h4
        refine ⟨u, Finset.mem_singleton_self _, ?_⟩
        have hnvS : (n, v) ∈ S_pub := (hπsub _ _ hedge).2
        exact mem_witness_agreement hdep₁ hu₁ hnvS hedge
    · -- source is a agreement: no outgoing edges
      rcases hdep' with ⟨p₁, q₁, _, _, _, _, heq⟩ |
          ⟨n₁, v₁, m₁, vs₁, q₁, _, _, _, heq⟩ |
          ⟨n₁, v₁, m₁, vs₁, q₁, u₁, _, _, _, _, heq⟩ |
          ⟨n₁, v₁, m₁, vs₁, q₁, u₁, _, _, _, _, heq⟩
      · simp only [Prod.mk.injEq] at heq
        exact absurd heq.1.1 (hvn.agreementN_ne_occurrenceN _ _ _ _ _)
      · simp only [Prod.mk.injEq] at heq
        exact absurd heq.1.1.symm (hvn.occurrenceN_ne_agreementN _ _ _ _ _)
      · simp only [Prod.mk.injEq] at heq
        exact absurd heq.1.1 (hvn.agreementN_ne_intermediateN _ _ _ _ _ _ _)
      · simp only [Prod.mk.injEq] at heq
        exact absurd heq.1.1 (hvn.agreementN_ne_intermediateN _ _ _ _ _ _ _)
  · -- version_unique
    intro pkg w₁ w₂ h₁ h₂
    rcases witness_mem_cases h₁ with
      ⟨n₁, w₁', q₁, hpS₁, hq₁, horigin₁, hins₁, heq₁⟩ |
      ⟨n₁, v₁, m₁, vs₁, q₁, u₁, hdep₁, hq₁, hu₁, horigin₁, hins₁, he₁, hedge₁, heq₁⟩ |
      ⟨n₁, v₁, m₁, vs₁, u₁, hdep₁, hu₁, hnv₁, hedge₁, heq₁⟩ <;>
    rcases witness_mem_cases h₂ with
      ⟨n₂, w₂', q₂, hpS₂, hq₂, horigin₂, hins₂, heq₂⟩ |
      ⟨n₂, v₂, m₂, vs₂, q₂, u₂, hdep₂, hq₂, hu₂, horigin₂, hins₂, he₂, hedge₂, heq₂⟩ |
      ⟨n₂, v₂, m₂, vs₂, u₂, hdep₂, hu₂, hnv₂, hedge₂, heq₂⟩ <;>
    simp only [Prod.mk.injEq] at heq₁ heq₂ <;>
    obtain ⟨he₁', rfl⟩ := heq₁ <;> obtain ⟨he₂', rfl⟩ := heq₂
    -- 9 cases by source component; 6 are name clashes
    · -- occurrence × occurrence: version visibility at the agreement origin
      obtain ⟨rfl, rfl⟩ := hvn.occurrenceN_injective _ _ _ _ (he₁'.symm.trans he₂')
      exact hres.version_visibility q₁ (horigin₁.mem hrS) n₁ w₁ w₂ hins₁ hins₂
    · exact absurd (he₁'.symm.trans he₂')
        (hvn.occurrenceN_ne_intermediateN _ _ _ _ _ _)
    · exact absurd (he₁'.symm.trans he₂')
        (hvn.occurrenceN_ne_agreementN _ _ _ _ _)
    · exact absurd (he₁'.symm.trans he₂')
        (hvn.intermediateN_ne_occurrenceN _ _ _ _ _ _)
    · -- intermediate × intermediate: functionality of the parent relation
      obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        hvn.intermediateN_injective _ _ _ _ _ _ _ _ (he₁'.symm.trans he₂')
      obtain rfl := hfn _ _ _ _ hdep₁ hdep₂
      obtain ⟨u₀, -, huniq⟩ :=
        hres.concurrent.parent_closure _ ((hπsub _ _ hedge₁).2) _ _ hdep₁
      have hw₁ := huniq w₁ ⟨hu₁, (hπsub _ _ hedge₁).1, hedge₁⟩
      have hw₂ := huniq w₂ ⟨hu₂, (hπsub _ _ hedge₂).1, hedge₂⟩
      exact hw₁.trans hw₂.symm
    · exact absurd (he₁'.symm.trans he₂')
        (hvn.intermediateN_ne_agreementN _ _ _ _ _ _ _)
    · exact absurd (he₁'.symm.trans he₂')
        (hvn.agreementN_ne_occurrenceN _ _ _ _ _)
    · exact absurd (he₁'.symm.trans he₂')
        (hvn.agreementN_ne_intermediateN _ _ _ _ _ _ _)
    · -- agreement × agreement: functionality of the parent relation
      obtain ⟨rfl, rfl, rfl⟩ := hvn.agreementN_injective _ _ _ _ _ _ (he₁'.symm.trans he₂')
      obtain rfl := hfn _ _ _ _ hdep₁ hdep₂
      obtain ⟨u₀, -, huniq⟩ :=
        hres.concurrent.parent_closure _ hnv₁ _ _ hdep₁
      have hw₁ := huniq w₁ ⟨hu₁, (hπsub _ _ hedge₁).1, hedge₁⟩
      have hw₂ := huniq w₂ ⟨hu₂, (hπsub _ _ hedge₂).1, hedge₂⟩
      exact hw₁.trans hw₂.symm

end PackageCalculus.Visibility
