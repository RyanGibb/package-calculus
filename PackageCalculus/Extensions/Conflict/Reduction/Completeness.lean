import PackageCalculus.Extensions.Conflict.Reduction.Definition

/-! # Conflict extension: completeness

Any conflict resolution lifts to a core resolution of the conflict
encoding. -/

namespace PackageCalculus.Conflict

open Classical

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcn : HasConflictNames N V N'] [hcv : HasConflictVersions V V']

def completenessWitness (S_Γ : Finset (Package N V)) (Γ : ConflictRel N V) :
    Finset (Package N' V') :=
  embedSet S_Γ ∪
  (Γ.filter (fun ⟨p, _, _⟩ => p ∈ S_Γ)).image (fun ⟨_, n, vs⟩ =>
    (hcn.syntheticN n vs, hcv.oneV)) ∪
  (Γ.filter (fun ⟨_, n, vs⟩ => ∃ u ∈ vs, (n, u) ∈ S_Γ)).image (fun ⟨_, n, vs⟩ =>
    (hcn.syntheticN n vs, hcv.zeroV))

private theorem mem_completenessWitness_embed {S_Γ : Finset (Package N V)} {Γ : ConflictRel N V}
    {p : Package N V} (hp : p ∈ S_Γ) :
    (embedPkg (N' := N') (V' := V') p) ∈ completenessWitness S_Γ Γ :=
  Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
    (Finset.mem_image_of_mem embedPkg hp))))

private theorem mem_completenessWitness_one {S_Γ : Finset (Package N V)} {Γ : ConflictRel N V}
    {p : Package N V} {n : N} {vs : Finset V}
    (hg : (p, n, vs) ∈ Γ) (hp : p ∈ S_Γ) :
    (hcn.syntheticN n vs, hcv.oneV) ∈ completenessWitness S_Γ Γ := by
  simp only [completenessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  left; right
  exact ⟨⟨p, n, vs⟩, ⟨hg, hp⟩, rfl⟩

private theorem mem_completenessWitness_zero {S_Γ : Finset (Package N V)} {Γ : ConflictRel N V}
    {p : Package N V} {n : N} {vs : Finset V}
    (hg : (p, n, vs) ∈ Γ) (hc : ∃ u ∈ vs, (n, u) ∈ S_Γ) :
    (hcn.syntheticN n vs, hcv.zeroV) ∈ completenessWitness S_Γ Γ := by
  simp only [completenessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  right
  exact ⟨⟨p, n, vs⟩, ⟨hg, hc⟩, rfl⟩

-- Helper: no element of conflictDeps has a syntheticN name as the package name component
omit [DecidableEq N] [DecidableEq V] in
private theorem no_synthetic_pkg_in_conflictDeps {Δ_Γ : DepRel N V} {Γ : ConflictRel N V}
    {n₀ : N} {vs₀ : Finset V} {v₀ : V'} {m : N'} {ws : Finset V'}
    (hd : ((hcn.syntheticN n₀ vs₀, v₀), m, ws) ∈ conflictDeps Δ_Γ Γ) : False := by
  simp only [conflictDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hd
  rcases hd with ((⟨a, _, heq⟩ | ⟨a, _, heq⟩) | ⟨a, _, _, _, heq⟩)
  all_goals simp only [embedPkg, Prod.mk.injEq] at heq
  -- heq.1.1 : origN a._._ = syntheticN n₀ vs₀
  · exact absurd heq.1.1 (hcn.origN_ne_syntheticN _ _ _)
  · exact absurd heq.1.1 (hcn.origN_ne_syntheticN _ _ _)
  · exact absurd heq.1.1 (hcn.origN_ne_syntheticN _ _ _)

-- Paper Thm 4.1.5 (Conflict Reduction Completeness).
theorem conflict_completeness
    (R_Γ : Real N V) (Δ_Γ : DepRel N V) (Γ : ConflictRel N V)
    (r : Package N V) (S_Γ : Finset (Package N V))
    (hres : IsConflictResolution R_Γ Δ_Γ Γ r S_Γ) :
    IsResolution (conflictReal R_Γ Γ) (conflictDeps Δ_Γ Γ) (embedPkg r)
      (completenessWitness S_Γ Γ) := by
  obtain ⟨⟨hsub, hroot, hdep, huniq⟩, havoid⟩ := hres
  refine ⟨?_, mem_completenessWitness_embed hroot, ?_, ?_⟩
  · -- subset
    intro q hq
    simp only [completenessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      embedSet] at hq
    simp only [conflictReal, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, embedSet]
    rcases hq with ((⟨p, hp, rfl⟩ | ⟨⟨p, n, vs⟩, ⟨hg, _⟩, rfl⟩) |
        ⟨⟨p, n, vs⟩, ⟨hg, _⟩, rfl⟩)
    · left; exact ⟨p, hsub hp, rfl⟩
    · right; exact ⟨⟨p, n, vs⟩, hg, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))⟩
    · right; exact ⟨⟨p, n, vs⟩, hg, Finset.mem_insert.mpr (Or.inl rfl)⟩
  · -- dep_closure
    intro q hq m ws hd
    simp only [completenessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      embedSet] at hq
    rcases hq with ((⟨p, hp, rfl⟩ | ⟨⟨p₀, n₀, vs₀⟩, ⟨_, hpS₀⟩, rfl⟩) |
        ⟨⟨p₀, n₀, vs₀⟩, ⟨_, _⟩, rfl⟩)
    · -- q = embedPkg p, p ∈ S_Γ
      simp only [conflictDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hd
      rcases hd with ((⟨a, hm, heq⟩ | ⟨a, hg', heq⟩) | ⟨a, hg', u', hu', heq⟩)
      · -- original dep
        simp only [embedPkg, Prod.mk.injEq] at heq
        obtain ⟨⟨h1, h2⟩, rfl, rfl⟩ := heq
        have h1' := hcn.origN.injective h1; have h2' := hcv.origV.injective h2
        have hp' : a.1 = p := Prod.ext h1' h2'
        subst hp'
        obtain ⟨v, hv, hvS⟩ := hdep _ hp _ _ hm
        exact ⟨hcv.origV v, Finset.mem_map.mpr ⟨v, hv, rfl⟩, mem_completenessWitness_embed hvS⟩
      · -- conflict dep
        simp only [embedPkg, Prod.mk.injEq] at heq
        obtain ⟨⟨h1, h2⟩, rfl, rfl⟩ := heq
        have h1' := hcn.origN.injective h1; have h2' := hcv.origV.injective h2
        have hp' : a.1 = p := Prod.ext h1' h2'
        subst hp'
        exact ⟨hcv.oneV, Finset.mem_singleton.mpr rfl, mem_completenessWitness_one hg' hp⟩
      · -- conflictee dep: embedPkg (n, u) -> syntheticN n vs -> zeroV
        -- heq : ((origN a.2.1, origV u'), syntheticN a.2.1 a.2.2, {zeroV}) = (embedPkg p, m, ws)
        simp only [embedPkg, Prod.mk.injEq] at heq
        obtain ⟨⟨h1, h2⟩, rfl, rfl⟩ := heq
        have hn := hcn.origN.injective h1
        have hv := hcv.origV.injective h2
        -- hn : a.2.1 = p.1, hv : u' = p.2
        -- Need: mem_completenessWitness_zero hg' ⟨p.2, _, hp⟩
        -- where _ proves p.2 ∈ a.2.2
        -- We have hu' : u' ∈ a.2.2
        subst hv -- now u' is gone, replaced by p.2
        have hp' : (a.2.1, p.2) ∈ S_Γ := hn ▸ hp
        exact ⟨hcv.zeroV, Finset.mem_singleton.mpr rfl,
               mem_completenessWitness_zero hg' ⟨p.2, hu', hp'⟩⟩
    · exact absurd (no_synthetic_pkg_in_conflictDeps hd) False.elim
    · exact absurd (no_synthetic_pkg_in_conflictDeps hd) False.elim
  · -- version_unique
    intro nm v1 v2 hv1 hv2
    simp only [completenessWitness, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      embedSet] at hv1 hv2
    rcases hv1 with ((⟨p₁, hp₁, heq1⟩ | ⟨⟨q₁, n₁, vs₁⟩, ⟨hg₁, hpS₁⟩, heq1⟩) |
        ⟨⟨q₁, n₁, vs₁⟩, ⟨hg₁, hc₁⟩, heq1⟩) <;>
    rcases hv2 with ((⟨p₂, hp₂, heq2⟩ | ⟨⟨q₂, n₂, vs₂⟩, ⟨hg₂, hpS₂⟩, heq2⟩) |
        ⟨⟨q₂, n₂, vs₂⟩, ⟨hg₂, hc₂⟩, heq2⟩)
    · -- orig x orig
      simp only [embedPkg, Prod.mk.injEq] at heq1 heq2
      rw [← heq1.2, ← heq2.2]
      exact congrArg _ (huniq p₁.1 p₁.2 p₂.2 hp₁
        (hcn.origN.injective (heq1.1.trans heq2.1.symm) ▸ hp₂))
    · -- orig x one
      simp only [embedPkg, Prod.mk.injEq] at heq1
      simp only [Prod.mk.injEq] at heq2
      exact absurd (heq1.1.trans heq2.1.symm) (hcn.origN_ne_syntheticN _ _ _)
    · -- orig x zero
      simp only [embedPkg, Prod.mk.injEq] at heq1
      simp only [Prod.mk.injEq] at heq2
      exact absurd (heq1.1.trans heq2.1.symm) (hcn.origN_ne_syntheticN _ _ _)
    · -- one x orig
      simp only [Prod.mk.injEq] at heq1
      simp only [embedPkg, Prod.mk.injEq] at heq2
      exact absurd (heq2.1.trans heq1.1.symm) (hcn.origN_ne_syntheticN _ _ _)
    · -- one x one
      simp only [Prod.mk.injEq] at heq1 heq2
      exact heq1.2.symm.trans heq2.2
    · -- one x zero: conflict avoidance
      simp only [Prod.mk.injEq] at heq1 heq2
      exfalso
      obtain ⟨rfl, rfl⟩ := hcn.syntheticN_injective (heq1.1.trans heq2.1.symm)
      exact havoid _ hpS₁ _ _ hg₁ hc₂
    · -- zero x orig
      simp only [Prod.mk.injEq] at heq1
      simp only [embedPkg, Prod.mk.injEq] at heq2
      exact absurd (heq2.1.trans heq1.1.symm) (hcn.origN_ne_syntheticN _ _ _)
    · -- zero x one: conflict avoidance
      simp only [Prod.mk.injEq] at heq1 heq2
      exfalso
      obtain ⟨rfl, rfl⟩ := hcn.syntheticN_injective (heq1.1.trans heq2.1.symm)
      exact havoid _ hpS₂ _ _ hg₂ hc₁
    · -- zero x zero
      simp only [Prod.mk.injEq] at heq1 heq2
      exact heq1.2.symm.trans heq2.2

end PackageCalculus.Conflict
