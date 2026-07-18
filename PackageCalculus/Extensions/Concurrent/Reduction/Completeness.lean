import PackageCalculus.Extensions.Concurrent.Reduction.Definition

/-! # Concurrent extension: completeness

Any concurrent resolution can be expanded into a core resolution of the
concurrent encoding. -/

namespace PackageCalculus.Concurrent

open Classical

set_option linter.unusedSectionVars false

variable {N : Type*} {V : Type*} {G : Type*}
variable {N' : Type*} {V' : Type*}
variable [DecidableEq N] [DecidableEq V] [DecidableEq G] [DecidableEq N'] [DecidableEq V']
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

def completenessWitness (S_C : Finset (Package N V))
    (π : Finset (Package N V × Package N V))
    (Δ_C : DepRel N V) (g : V → G) :
    Finset (Package N' V') :=
  -- Granular packages: (⟨n, g(v)⟩, orig v) for (n, v) ∈ S_C
  S_C.image (fun ⟨n, v⟩ => (hcnm.granularN n (g v), hcvr.origV v)) ∪
  -- Intermediate packages for split case:
  -- (⟨n, v, m⟩, gran (g u)) where ((n,v),m,vs) ∈ Δ_C, isSplit, (n,v) ∈ S_C,
  -- (m,u) ∈ S_C, u ∈ vs, ((m,u),(n,v)) ∈ π
  (Δ_C.biUnion (fun ⟨⟨n, v⟩, m, vs⟩ =>
    if isSplit g vs ∧ (n, v) ∈ S_C then
      (vs.filter (fun u => (m, u) ∈ S_C ∧ ((m, u), (n, v)) ∈ π)).image
        (fun u => (hcnm.intermediateN n v m, hcvr.granV (g u)))
    else ∅))

theorem mem_gran {S_C : Finset (Package N V)}
    {π : Finset (Package N V × Package N V)}
    {Δ_C : DepRel N V} {g : V → G}
    {n : N} {v : V} (h : (n, v) ∈ S_C) :
    (hcnm.granularN n (g v), hcvr.origV v) ∈
      completenessWitness S_C π Δ_C g :=
  Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨⟨n, v⟩, h, rfl⟩))

theorem mem_inter {S_C : Finset (Package N V)}
    {π : Finset (Package N V × Package N V)}
    {Δ_C : DepRel N V} {g : V → G}
    {n : N} {v : V} {m : N} {vs : Finset V} {u : V}
    (hdep : ((n, v), m, vs) ∈ Δ_C) (hnv : (n, v) ∈ S_C)
    (hspl : isSplit g vs) (hmu : (m, u) ∈ S_C) (hu : u ∈ vs)
    (hπ : ((m, u), (n, v)) ∈ π) :
    (hcnm.intermediateN n v m, hcvr.granV (g u)) ∈
      completenessWitness S_C π Δ_C g := by
  simp only [completenessWitness, Finset.mem_union, Finset.mem_biUnion]
  right
  refine ⟨⟨⟨n, v⟩, m, vs⟩, hdep, ?_⟩
  simp only
  rw [if_pos ⟨hspl, hnv⟩]
  exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hmu, hπ⟩, rfl⟩

theorem completenessWitness_mem_cases {S_C : Finset (Package N V)}
    {π : Finset (Package N V × Package N V)}
    {Δ_C : DepRel N V} {g : V → G}
    {q : Package N' V'} (hq : q ∈ completenessWitness S_C π Δ_C g) :
    (∃ n v, (n, v) ∈ S_C ∧ q = (hcnm.granularN n (g v), hcvr.origV v)) ∨
    (∃ n v m vs u, ((n, v), m, vs) ∈ Δ_C ∧ (n, v) ∈ S_C ∧ isSplit g vs ∧
      (m, u) ∈ S_C ∧ u ∈ vs ∧ ((m, u), (n, v)) ∈ π ∧
      q = (hcnm.intermediateN n v m, hcvr.granV (g u))) := by
  simp only [completenessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hq
  rcases hq with ⟨⟨n, v⟩, hmem, rfl⟩ | ⟨⟨⟨n, v⟩, m, vs⟩, hdep, hmem⟩
  · exact Or.inl ⟨n, v, hmem, rfl⟩
  · right
    simp only at hmem
    split at hmem
    case isTrue h =>
      obtain ⟨hspl, hnv⟩ := h
      simp only [Finset.mem_image, Finset.mem_filter] at hmem
      obtain ⟨u, ⟨hu, hmu, hπ⟩, rfl⟩ := hmem
      exact ⟨n, v, m, vs, u, hdep, hnv, hspl, hmu, hu, hπ, rfl⟩
    case isFalse => exact (List.mem_nil_iff _ |>.mp hmem).elim

theorem concurrent_completeness
    (R_C : Real N V) (Δ_C : DepRel N V)
    (g : V → G) (r : Package N V)
    (S_C : Finset (Package N V))
    (π : Finset (Package N V × Package N V))
    (hres : IsConcurrentResolution R_C Δ_C g r S_C π)
    (hfunc : Δ_C.FunctionalInName) :
    IsResolution (concurrentReal R_C Δ_C g) (concurrentDeps Δ_C g)
      (embedPkg g r) (completenessWitness S_C π Δ_C g) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- subset
    intro q hq
    rcases completenessWitness_mem_cases hq with
      ⟨n, v, hmem, rfl⟩ | ⟨n, v, m, vs, u, hdep, hnv, hspl, hmu, hu, hπ, rfl⟩
    · simp only [concurrentReal, embedReal, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
      left; exact ⟨⟨n, v⟩, hres.subset hmem, rfl⟩
    · simp only [concurrentReal, embedReal, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
      right
      refine ⟨⟨⟨n, v⟩, m, vs⟩, hdep, ?_⟩
      simp only; rw [if_pos hspl]
      exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  · -- root_mem
    obtain ⟨rn, rv⟩ := r
    exact mem_gran hres.root_mem
  · -- dep_closure
    intro q hq m_dep dep_vs hd
    rcases completenessWitness_mem_cases hq with
      ⟨n, v, hmem, rfl⟩ | ⟨n, v, m, vs, u, hdep, hnv, hspl, hmu, hu, hπ, rfl⟩
    · -- granular package (granularN n (g v), origV v)
      simp only [concurrentDeps, Finset.mem_union, Finset.mem_biUnion] at hd
      rcases hd with (((⟨a, haΔ, hmem_d⟩ | ⟨a, haΔ, hmem_d⟩) | ⟨a, haΔ, hmem_d⟩) | ⟨a, haΔ, hmem_d⟩)
      · -- direct case
        obtain ⟨⟨n', v'⟩, m', vs'⟩ := a
        simp only at hmem_d; split at hmem_d
        case isTrue hdir =>
          simp only [Finset.mem_image, Prod.mk.injEq] at hmem_d
          obtain ⟨u', hu', ⟨⟨h1, h2⟩, rfl, rfl⟩⟩ := hmem_d
          have ⟨h1a, _⟩ := hcnm.granularN_injective h1; subst h1a
          have h2' := hcvr.origV.injective h2; subst h2'
          obtain ⟨u, ⟨huv, hmuS, _⟩, _⟩ := hres.parent_closure _ hmem _ _ haΔ
          refine ⟨hcvr.origV u, Finset.mem_map.mpr ⟨u, huv, rfl⟩, ?_⟩
          have hgu_eq : g u = g u' := hdir u u' huv hu'
          exact hgu_eq ▸ mem_gran hmuS
        case isFalse => exact (List.mem_nil_iff _ |>.mp hmem_d).elim
      · -- split depender→intermediate
        obtain ⟨⟨n', v'⟩, m', vs'⟩ := a
        simp only at hmem_d; split at hmem_d
        case isTrue hspl =>
          simp only [Finset.mem_singleton, Prod.mk.injEq] at hmem_d
          obtain ⟨⟨h1, h2⟩, rfl, rfl⟩ := hmem_d
          have ⟨h1a, _⟩ := hcnm.granularN_injective h1; subst h1a
          have h2' := hcvr.origV.injective h2; subst h2'
          obtain ⟨u, ⟨huv, hmuS, hmuπ⟩, _⟩ := hres.parent_closure _ hmem _ _ haΔ
          refine ⟨hcvr.granV (g u),
            Finset.mem_map.mpr ⟨g u, Finset.mem_image.mpr ⟨u, huv, rfl⟩, rfl⟩,
            mem_inter haΔ hmem hspl hmuS huv hmuπ⟩
        case isFalse => exact (List.mem_nil_iff _ |>.mp hmem_d).elim
      · -- split intermediate→dependee: source is granular, contradiction
        obtain ⟨⟨n', v'⟩, m', vs'⟩ := a
        simp only at hmem_d; split at hmem_d
        case isTrue =>
          simp only [Finset.mem_image, Prod.mk.injEq] at hmem_d
          obtain ⟨_, _, ⟨⟨h1, _⟩, _, _⟩⟩ := hmem_d
          exact absurd h1 (hcnm.intermediateN_ne_granularN _ _ _ _ _)
        case isFalse => exact (List.mem_nil_iff _ |>.mp hmem_d).elim
      · -- empty case: selected depender contradicts parent closure on ∅
        obtain ⟨⟨n', v'⟩, m', vs'⟩ := a
        simp only at hmem_d; split at hmem_d
        case isTrue hemp =>
          simp only [Finset.mem_singleton, Prod.mk.injEq] at hmem_d
          obtain ⟨⟨h1, h2⟩, rfl, rfl⟩ := hmem_d
          have ⟨h1a, _⟩ := hcnm.granularN_injective h1; subst h1a
          have h2' := hcvr.origV.injective h2; subst h2'
          subst hemp
          obtain ⟨u, ⟨huv, _, _⟩, _⟩ := hres.parent_closure _ hmem _ _ haΔ
          exact absurd huv (Finset.notMem_empty u)
        case isFalse => exact (List.mem_nil_iff _ |>.mp hmem_d).elim
    · -- intermediate package (intermediateN n v m, granV (g u))
      simp only [concurrentDeps, Finset.mem_union, Finset.mem_biUnion] at hd
      rcases hd with (((⟨a, haΔ, hmem_d⟩ | ⟨a, haΔ, hmem_d⟩) | ⟨a, haΔ, hmem_d⟩) | ⟨a, haΔ, hmem_d⟩)
      · -- direct case: intermediateN = granularN, contradiction
        obtain ⟨⟨n', v'⟩, m', vs'⟩ := a
        simp only at hmem_d; split at hmem_d
        case isTrue =>
          simp only [Finset.mem_image, Prod.mk.injEq] at hmem_d
          obtain ⟨_, _, ⟨⟨h1, _⟩, _, _⟩⟩ := hmem_d
          exact absurd h1 (hcnm.granularN_ne_intermediateN _ _ _ _ _)
        case isFalse => exact (List.mem_nil_iff _ |>.mp hmem_d).elim
      · -- split depender→intermediate: intermediateN = granularN, contradiction
        obtain ⟨⟨n', v'⟩, m', vs'⟩ := a
        simp only at hmem_d; split at hmem_d
        case isTrue =>
          simp only [Finset.mem_singleton, Prod.mk.injEq] at hmem_d
          obtain ⟨⟨h1, _⟩, _, _⟩ := hmem_d
          exact absurd h1 (hcnm.intermediateN_ne_granularN _ _ _ _ _)
        case isFalse => exact (List.mem_nil_iff _ |>.mp hmem_d).elim
      · -- split intermediate→dependee
        obtain ⟨⟨n', v'⟩, m', vs'⟩ := a
        simp only at hmem_d; split at hmem_d
        case isTrue hspl' =>
          simp only [Finset.mem_image, Prod.mk.injEq] at hmem_d
          obtain ⟨u', hu'vs, ⟨⟨h1, h2⟩, rfl, rfl⟩⟩ := hmem_d
          -- h1 : intermediateN n' v' m' = intermediateN n v m
          -- After injective: n' = n, v' = v, m' = m
          obtain ⟨rfl, rfl, rfl⟩ := hcnm.intermediateN_injective _ _ _ _ _ _ h1.symm
          have hgu := hcvr.granV.injective h2
          have hvs := hfunc _ _ _ _ hdep haΔ; subst hvs
          refine ⟨hcvr.origV u,
            Finset.mem_map.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hgu.symm⟩, rfl⟩,
            hgu.symm ▸ mem_gran hmu⟩
        case isFalse => exact (List.mem_nil_iff _ |>.mp hmem_d).elim
      · -- empty case: depender is granular, name clash
        obtain ⟨⟨n', v'⟩, m', vs'⟩ := a
        simp only at hmem_d; split at hmem_d
        case isTrue =>
          simp only [Finset.mem_singleton, Prod.mk.injEq] at hmem_d
          obtain ⟨⟨h1, _⟩, _, _⟩ := hmem_d
          exact absurd h1 (hcnm.intermediateN_ne_granularN _ _ _ _ _)
        case isFalse => exact (List.mem_nil_iff _ |>.mp hmem_d).elim
  · -- version_unique
    intro nm cv₁ cv₂ hv₁ hv₂
    rcases completenessWitness_mem_cases hv₁ with
      ⟨n₁, v₁, hmem₁, heq1⟩ | ⟨n₁, vp₁, m₁, vs₁, u₁, hd₁, hnv₁, _, hmu₁, hu₁, hπ₁, heq1⟩ <;>
    rcases completenessWitness_mem_cases hv₂ with
      ⟨n₂, v₂, hmem₂, heq2⟩ | ⟨n₂, vp₂, m₂, vs₂, u₂, hd₂, hnv₂, _, hmu₂, hu₂, hπ₂, heq2⟩ <;>
    simp only [Prod.mk.injEq] at heq1 heq2
    · -- granular × granular
      obtain ⟨h1n, rfl⟩ := heq1; obtain ⟨h2n, rfl⟩ := heq2
      have ⟨rfl, h1g⟩ := hcnm.granularN_injective (h1n.symm.trans h2n)
      by_contra hne
      have hne' : v₁ ≠ v₂ := fun h => hne (congrArg hcvr.origV h)
      exact hres.version_granularity _ _ _ hmem₁ hmem₂ hne' h1g
    · -- granular × intermediate: name clash
      obtain ⟨h1n, _⟩ := heq1; obtain ⟨h2n, _⟩ := heq2
      exact absurd (h1n.symm.trans h2n) (hcnm.granularN_ne_intermediateN _ _ _ _ _)
    · -- intermediate × granular: name clash
      obtain ⟨h1n, _⟩ := heq1; obtain ⟨h2n, _⟩ := heq2
      exact absurd (h1n.symm.trans h2n) (hcnm.intermediateN_ne_granularN _ _ _ _ _)
    · -- intermediate × intermediate
      obtain ⟨h1n, rfl⟩ := heq1; obtain ⟨h2n, rfl⟩ := heq2
      obtain ⟨rfl, rfl, rfl⟩ := hcnm.intermediateN_injective _ _ _ _ _ _ (h1n.symm.trans h2n)
      have hvs := hfunc (n₁, vp₁) m₁ vs₁ vs₂ hd₁ hd₂; subst hvs
      obtain ⟨w, _, huniq⟩ := hres.parent_closure _ hnv₁ _ _ hd₁
      have h1 := huniq u₁ ⟨hu₁, hmu₁, hπ₁⟩
      have h2 := huniq u₂ ⟨hu₂, hmu₂, hπ₂⟩
      exact congrArg hcvr.granV (congrArg g (h1.trans h2.symm))

end PackageCalculus.Concurrent
