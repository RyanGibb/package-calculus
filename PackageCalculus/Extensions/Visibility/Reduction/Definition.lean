import PackageCalculus.Extensions.Visibility.Definition

/-! # Visibility extension: reduction -/

namespace PackageCalculus.Visibility

open PackageCalculus

inductive VisibilityName (N V : Type*) where
  | occurrence : N → N × V → VisibilityName N V
  | intermediate : N → V → N → N × V → VisibilityName N V
  | agreement : N → V → N → VisibilityName N V
  deriving DecidableEq

class HasVisibilityNames (N V : Type*) (N' : outParam Type*) where
  occurrenceN : N → Package N V → N'
  occurrenceN_injective : ∀ n₁ q₁ n₂ q₂, occurrenceN n₁ q₁ = occurrenceN n₂ q₂ → n₁ = n₂ ∧ q₁ = q₂
  intermediateN : N → V → N → Package N V → N'
  intermediateN_injective : ∀ n₁ v₁ m₁ q₁ n₂ v₂ m₂ q₂,
    intermediateN n₁ v₁ m₁ q₁ = intermediateN n₂ v₂ m₂ q₂ →
    n₁ = n₂ ∧ v₁ = v₂ ∧ m₁ = m₂ ∧ q₁ = q₂
  agreementN : N → V → N → N'
  agreementN_injective : ∀ n₁ v₁ m₁ n₂ v₂ m₂,
    agreementN n₁ v₁ m₁ = agreementN n₂ v₂ m₂ → n₁ = n₂ ∧ v₁ = v₂ ∧ m₁ = m₂
  occurrenceN_ne_intermediateN : ∀ n q n' v m q', occurrenceN n q ≠ intermediateN n' v m q'
  intermediateN_ne_occurrenceN : ∀ n v m q n' q', intermediateN n v m q ≠ occurrenceN n' q'
  occurrenceN_ne_agreementN : ∀ n q n' v m, occurrenceN n q ≠ agreementN n' v m
  agreementN_ne_occurrenceN : ∀ n v m n' q, agreementN n v m ≠ occurrenceN n' q
  intermediateN_ne_agreementN : ∀ n v m q n' v' m', intermediateN n v m q ≠ agreementN n' v' m'
  agreementN_ne_intermediateN : ∀ n v m n' v' m' q, agreementN n v m ≠ intermediateN n' v' m' q

attribute [simp] HasVisibilityNames.occurrenceN_ne_intermediateN HasVisibilityNames.intermediateN_ne_occurrenceN
  HasVisibilityNames.occurrenceN_ne_agreementN HasVisibilityNames.agreementN_ne_occurrenceN
  HasVisibilityNames.intermediateN_ne_agreementN HasVisibilityNames.agreementN_ne_intermediateN

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N']
variable [hvn : HasVisibilityNames N V N']

variable (R_C : Real N V) (Δ : DepRel N V) (pub : PubRel N V) (r : Package N V)

def potentialOrigins (R_C : Real N V) (Δ : DepRel N V) (pub : PubRel N V)
    (r : Package N V) : Finset (Package N V) :=
  insert r (R_C.filter (Priv Δ pub))

/-- A dependency's edge is carried at occurrence q when it is public or q is the depender. -/
def carried (p : Package N V) (m : N) (q : Package N V) : Prop :=
  (p, m) ∈ pub ∨ p = q

instance {p : Package N V} {m : N} {q : Package N V} :
    Decidable (carried pub p m q) := by
  unfold carried; infer_instance

def visRoot : Package N' V := (hvn.occurrenceN r.1 r, r.2)

def visReal : Real N' V :=
  -- Occurrences
  (R_C.biUnion fun p => (potentialOrigins R_C Δ pub r).image
    fun q => (hvn.occurrenceN p.1 q, p.2)) ∪
  -- Per-occurrence intermediates
  (Δ.biUnion fun ⟨⟨n, v⟩, m, vs⟩ => (potentialOrigins R_C Δ pub r).biUnion
    fun q => vs.image fun u => (hvn.intermediateN n v m q, u)) ∪
  -- Agreements
  (Δ.biUnion fun ⟨⟨n, v⟩, m, vs⟩ => vs.image fun u => (hvn.agreementN n v m, u))

def visDeps : DepRel N' V :=
  -- Self-occurrence driving: every occurrence of a private-depender requires its own occurrence
  (R_C.biUnion fun p => (potentialOrigins R_C Δ pub r).biUnion fun q =>
    if Priv Δ pub p ∧ q ≠ p then
      {((hvn.occurrenceN p.1 q, p.2), hvn.occurrenceN p.1 p, ({p.2} : Finset V))}
    else ∅) ∪
  -- Occurrence → intermediate
  (Δ.biUnion fun ⟨⟨n, v⟩, m, vs⟩ => (potentialOrigins R_C Δ pub r).biUnion fun q =>
    if carried pub (n, v) m q then {((hvn.occurrenceN n q, v), hvn.intermediateN n v m q, vs)}
    else ∅) ∪
  -- Intermediate → dependee occurrence at the same origin
  (Δ.biUnion fun ⟨⟨n, v⟩, m, vs⟩ => (potentialOrigins R_C Δ pub r).biUnion fun q =>
    if carried pub (n, v) m q then
      vs.image fun u => ((hvn.intermediateN n v m q, u), hvn.occurrenceN m q, ({u} : Finset V))
    else ∅) ∪
  -- Intermediate → agreement
  (Δ.biUnion fun ⟨⟨n, v⟩, m, vs⟩ => (potentialOrigins R_C Δ pub r).biUnion fun q =>
    if carried pub (n, v) m q then
      vs.image fun u => ((hvn.intermediateN n v m q, u), hvn.agreementN n v m, ({u} : Finset V))
    else ∅)

/-! ## Membership lemmas -/

section Membership

variable {R_C : Real N V} {Δ : DepRel N V} {pub : PubRel N V} {r : Package N V}

theorem mem_potentialOrigins {q : Package N V} :
    q ∈ potentialOrigins R_C Δ pub r ↔ q = r ∨ (q ∈ R_C ∧ Priv Δ pub q) := by
  simp [potentialOrigins]

theorem occurrence_mem_visReal {p q : Package N V}
    (hp : p ∈ R_C) (hq : q ∈ potentialOrigins R_C Δ pub r) :
    (hvn.occurrenceN p.1 q, p.2) ∈ visReal R_C Δ pub r (N' := N') := by
  simp only [visReal, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
  exact Or.inl (Or.inl ⟨p, hp, q, hq, rfl⟩)

theorem occurrence_mem_visReal_elim {n : N} {q : Package N V} {v : V}
    (h : (hvn.occurrenceN n q, v) ∈ visReal R_C Δ pub r (N' := N')) :
    (n, v) ∈ R_C ∧ q ∈ potentialOrigins R_C Δ pub r := by
  simp only [visReal, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at h
  rcases h with (⟨p, hp, q', hq', heq⟩ | ⟨⟨⟨n₁, v₁⟩, m₁, vs₁⟩, _, q', _, u, _, heq⟩) |
    ⟨⟨⟨n₁, v₁⟩, m₁, vs₁⟩, _, u, _, heq⟩
  · simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    obtain ⟨rfl, rfl⟩ := hvn.occurrenceN_injective _ _ _ _ h1
    exact ⟨h2 ▸ hp, hq'⟩
  · simp only [Prod.mk.injEq] at heq
    exact absurd heq.1 (hvn.intermediateN_ne_occurrenceN _ _ _ _ _ _)
  · simp only [Prod.mk.injEq] at heq
    exact absurd heq.1 (hvn.agreementN_ne_occurrenceN _ _ _ _ _)

theorem intermediate_mem_visReal {n : N} {v : V} {m : N} {vs : Finset V}
    {q : Package N V} {u : V}
    (hdep : ((n, v), m, vs) ∈ Δ) (hq : q ∈ potentialOrigins R_C Δ pub r) (hu : u ∈ vs) :
    (hvn.intermediateN n v m q, u) ∈ visReal R_C Δ pub r (N' := N') := by
  simp only [visReal, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
  exact Or.inl (Or.inr ⟨⟨(n, v), m, vs⟩, hdep, q, hq, u, hu, rfl⟩)

theorem agreement_mem_visReal {n : N} {v : V} {m : N} {vs : Finset V} {u : V}
    (hdep : ((n, v), m, vs) ∈ Δ) (hu : u ∈ vs) :
    (hvn.agreementN n v m, u) ∈ visReal R_C Δ pub r (N' := N') := by
  simp only [visReal, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
  exact Or.inr ⟨⟨(n, v), m, vs⟩, hdep, u, hu, rfl⟩

/-- Membership in `visDeps`, decomposed into its four edge families. -/
theorem mem_visDeps_iff {e : Package N' V × N' × Finset V} :
    e ∈ visDeps R_C Δ pub r (N' := N') ↔
      (∃ p q, p ∈ R_C ∧ q ∈ potentialOrigins R_C Δ pub r ∧ Priv Δ pub p ∧ q ≠ p ∧
        e = ((hvn.occurrenceN p.1 q, p.2), hvn.occurrenceN p.1 p, {p.2})) ∨
      (∃ n v m vs q, ((n, v), m, vs) ∈ Δ ∧ q ∈ potentialOrigins R_C Δ pub r ∧
        carried pub (n, v) m q ∧
        e = ((hvn.occurrenceN n q, v), hvn.intermediateN n v m q, vs)) ∨
      (∃ n v m vs q u, ((n, v), m, vs) ∈ Δ ∧ q ∈ potentialOrigins R_C Δ pub r ∧
        carried pub (n, v) m q ∧ u ∈ vs ∧
        e = ((hvn.intermediateN n v m q, u), hvn.occurrenceN m q, {u})) ∨
      (∃ n v m vs q u, ((n, v), m, vs) ∈ Δ ∧ q ∈ potentialOrigins R_C Δ pub r ∧
        carried pub (n, v) m q ∧ u ∈ vs ∧
        e = ((hvn.intermediateN n v m q, u), hvn.agreementN n v m, {u})) := by
  simp only [visDeps, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro (((⟨p, hp, q, hq, hif⟩ | ⟨⟨⟨n, v⟩, m, vs⟩, hdep, q, hq, hif⟩) |
      ⟨⟨⟨n, v⟩, m, vs⟩, hdep, q, hq, hif⟩) | ⟨⟨⟨n, v⟩, m, vs⟩, hdep, q, hq, hif⟩)
    · split_ifs at hif with hpriv
      · rw [Finset.mem_singleton] at hif
        exact Or.inl ⟨p, q, hp, hq, hpriv.1, hpriv.2, hif⟩
      · exact absurd hif (Finset.notMem_empty e)
    · split_ifs at hif with hedge
      · rw [Finset.mem_singleton] at hif
        exact Or.inr (Or.inl ⟨n, v, m, vs, q, hdep, hq, hedge, hif⟩)
      · exact absurd hif (Finset.notMem_empty e)
    · split_ifs at hif with hedge
      · rw [Finset.mem_image] at hif
        obtain ⟨u, hu, heq⟩ := hif
        exact Or.inr (Or.inr (Or.inl ⟨n, v, m, vs, q, u, hdep, hq, hedge, hu, heq.symm⟩))
      · exact absurd hif (Finset.notMem_empty e)
    · split_ifs at hif with hedge
      · rw [Finset.mem_image] at hif
        obtain ⟨u, hu, heq⟩ := hif
        exact Or.inr (Or.inr (Or.inr ⟨n, v, m, vs, q, u, hdep, hq, hedge, hu, heq.symm⟩))
      · exact absurd hif (Finset.notMem_empty e)
  · rintro (⟨p, q, hp, hq, hpriv, hne, rfl⟩ | ⟨n, v, m, vs, q, hdep, hq, hedge, rfl⟩ |
      ⟨n, v, m, vs, q, u, hdep, hq, hedge, hu, rfl⟩ |
      ⟨n, v, m, vs, q, u, hdep, hq, hedge, hu, rfl⟩)
    · refine Or.inl (Or.inl (Or.inl ⟨p, hp, q, hq, ?_⟩))
      rw [if_pos ⟨hpriv, hne⟩]
      exact Finset.mem_singleton_self _
    · refine Or.inl (Or.inl (Or.inr ⟨⟨(n, v), m, vs⟩, hdep, q, hq, ?_⟩))
      rw [if_pos hedge]
      exact Finset.mem_singleton_self _
    · refine Or.inl (Or.inr ⟨⟨(n, v), m, vs⟩, hdep, q, hq, ?_⟩)
      rw [if_pos hedge]
      rw [Finset.mem_image]
      exact ⟨u, hu, rfl⟩
    · refine Or.inr ⟨⟨(n, v), m, vs⟩, hdep, q, hq, ?_⟩
      rw [if_pos hedge]
      rw [Finset.mem_image]
      exact ⟨u, hu, rfl⟩

theorem mem_visDeps_self {p q : Package N V}
    (hp : p ∈ R_C) (hq : q ∈ potentialOrigins R_C Δ pub r) (hpriv : Priv Δ pub p)
    (hne : q ≠ p) :
    ((hvn.occurrenceN p.1 q, p.2), hvn.occurrenceN p.1 p, ({p.2} : Finset V)) ∈
      visDeps R_C Δ pub r (N' := N') :=
  mem_visDeps_iff.mpr (Or.inl ⟨p, q, hp, hq, hpriv, hne, rfl⟩)

theorem mem_visDeps_occ2int {n : N} {v : V} {m : N} {vs : Finset V} {q : Package N V}
    (hdep : ((n, v), m, vs) ∈ Δ) (hq : q ∈ potentialOrigins R_C Δ pub r)
    (he : carried pub (n, v) m q) :
    ((hvn.occurrenceN n q, v), hvn.intermediateN n v m q, vs) ∈ visDeps R_C Δ pub r (N' := N') :=
  mem_visDeps_iff.mpr (Or.inr (Or.inl ⟨n, v, m, vs, q, hdep, hq, he, rfl⟩))

theorem mem_visDeps_int2occ {n : N} {v : V} {m : N} {vs : Finset V} {q : Package N V} {u : V}
    (hdep : ((n, v), m, vs) ∈ Δ) (hq : q ∈ potentialOrigins R_C Δ pub r)
    (he : carried pub (n, v) m q) (hu : u ∈ vs) :
    ((hvn.intermediateN n v m q, u), hvn.occurrenceN m q, ({u} : Finset V)) ∈
      visDeps R_C Δ pub r (N' := N') :=
  mem_visDeps_iff.mpr (Or.inr (Or.inr (Or.inl ⟨n, v, m, vs, q, u, hdep, hq, he, hu, rfl⟩)))

theorem mem_visDeps_int2agr {n : N} {v : V} {m : N} {vs : Finset V} {q : Package N V} {u : V}
    (hdep : ((n, v), m, vs) ∈ Δ) (hq : q ∈ potentialOrigins R_C Δ pub r)
    (he : carried pub (n, v) m q) (hu : u ∈ vs) :
    ((hvn.intermediateN n v m q, u), hvn.agreementN n v m, ({u} : Finset V)) ∈
      visDeps R_C Δ pub r (N' := N') :=
  mem_visDeps_iff.mpr (Or.inr (Or.inr (Or.inr ⟨n, v, m, vs, q, u, hdep, hq, he, hu, rfl⟩)))

end Membership

end PackageCalculus.Visibility

namespace PackageCalculus

variable {N V : Type*}

instance : Visibility.HasVisibilityNames N V (Visibility.VisibilityName N V) where
  occurrenceN := Visibility.VisibilityName.occurrence
  intermediateN := Visibility.VisibilityName.intermediate
  agreementN := Visibility.VisibilityName.agreement
  occurrenceN_injective := fun _ _ _ _ h =>
    ⟨Visibility.VisibilityName.occurrence.inj h |>.1,
     Visibility.VisibilityName.occurrence.inj h |>.2⟩
  intermediateN_injective := fun _ _ _ _ _ _ _ _ h =>
    have := Visibility.VisibilityName.intermediate.inj h
    ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩
  agreementN_injective := fun _ _ _ _ _ _ h =>
    have := Visibility.VisibilityName.agreement.inj h
    ⟨this.1, this.2.1, this.2.2⟩
  occurrenceN_ne_intermediateN := fun _ _ _ _ _ _ => nofun
  intermediateN_ne_occurrenceN := fun _ _ _ _ _ _ => nofun
  occurrenceN_ne_agreementN := fun _ _ _ _ _ => nofun
  agreementN_ne_occurrenceN := fun _ _ _ _ _ => nofun
  intermediateN_ne_agreementN := fun _ _ _ _ _ _ _ => nofun
  agreementN_ne_intermediateN := fun _ _ _ _ _ _ _ => nofun

end PackageCalculus
