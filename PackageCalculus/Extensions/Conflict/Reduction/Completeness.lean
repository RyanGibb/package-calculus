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
  constructor;
  · intro p hp
    simp [completenessWitness, conflictReal] at hp ⊢
    generalize_proofs at *;
    rcases hp with ( hp | ⟨ a, b, a_1, b_1, ⟨ h₁, h₂ ⟩, rfl ⟩ | ⟨ a, b, a_1, b_1, ⟨ h₁, u, hu, h₂ ⟩, rfl ⟩ ) <;> simp_all +decide [ embedSet ];
    · rcases hp with ⟨ a, b, hp, rfl ⟩ ; exact Or.inl ⟨ a, b, hres.core.subset hp, rfl ⟩ ;
    · exact Or.inr ⟨ _, _, _, _, h₁, rfl ⟩;
    · exact Or.inr ⟨ _, _, _, _, h₁, rfl ⟩;
  · exact mem_completenessWitness_embed hres.core.root_mem;
  · intro p hp m vs h;
    unfold completenessWitness at *;
    unfold conflictDeps at h; simp_all +decide [ Finset.mem_union, Finset.mem_image ] ;
    rcases h with ( ⟨ a, b, a', b', h₁, rfl, rfl, rfl ⟩ | ⟨ a, b, a', b', h₁, rfl, rfl, rfl ⟩ | ⟨ a, b, a', b', h₁, u, hu, rfl, rfl, rfl ⟩ ) <;> simp_all +decide [ embedSet, embedPkg, embedVS ];
    · have := hres.core.dep_closure ( a, b ) hp a' b' h₁; aesop;
    · exact ⟨ _, _, _, _, ⟨ h₁, hp ⟩, rfl ⟩;
    · exact ⟨ _, _, _, _, ⟨ h₁, u, hu, hp ⟩, rfl ⟩;
  · intro n;
    unfold completenessWitness;
    simp +decide [ embedSet ];
    unfold embedPkg; simp +decide ;
    rintro v v' ( ⟨ a, b, hab, rfl, rfl ⟩ | ⟨ a, b, a', b', ⟨ h₁, h₂ ⟩, rfl, rfl ⟩ | ⟨ a, b, a', b', ⟨ h₁, u, hu, h₂ ⟩, rfl, rfl ⟩ ) ( ⟨ c, d, hcd, h₃, rfl ⟩ | ⟨ c, d, c', d', ⟨ h₄, h₅ ⟩, h₃, rfl ⟩ | ⟨ c, d, c', d', ⟨ h₄, u', hu', h₅ ⟩, h₃, rfl ⟩ ) <;> simp_all +decide [ hcv.zeroV_ne_oneV ];
    · exact hres.core.version_unique a b d hab hcd;
    · have := hres.conflict_avoidance _ h₂ _ _ h₁; simp_all +decide [ HasConflictNames.syntheticN_injective.eq_iff ] ;
    · have := hres.conflict_avoidance _ h₅ _ _ h₄; simp_all +decide [ hcn.syntheticN_injective.eq_iff ] ;

end PackageCalculus.Conflict