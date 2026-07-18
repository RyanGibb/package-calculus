import PackageCalculus.Extensions.Conflict.Reduction.Definition
import Mathlib.Data.Finset.Preimage

/-! # Conflict extension: soundness

Any core resolution of the conflict encoding induces a conflict resolution of
the original problem. -/

namespace PackageCalculus.Conflict

open Classical

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcn : HasConflictNames N V N'] [hcv : HasConflictVersions V V']

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem embedPkg_injective : Function.Injective (embedPkg : Package N V → Package N' V') := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [embedPkg, Prod.mk.injEq] at h
  exact Prod.ext (hcn.origN.injective h.1) (hcv.origV.injective h.2)

/-- Computable partial inverse of `embedPkg` via `tryOrigN`/`tryOrigV`. -/
def tryInvPkg (p : Package N' V') : Option (Package N V) :=
  match hcn.tryOrigN p.1, hcv.tryOrigV p.2 with
  | some n, some v => some (n, v)
  | _, _ => none

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem tryInvPkg_embed (p : Package N V) :
    tryInvPkg (embedPkg p) = some p := by
  simp [tryInvPkg, embedPkg, hcn.tryOrigN_origN, hcv.tryOrigV_origV]

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem tryInvPkg_some {p' : Package N' V'} {p : Package N V}
    (h : p ∈ tryInvPkg p') : embedPkg p = p' := by
  obtain ⟨n', v'⟩ := p'
  obtain ⟨n, v⟩ := p
  simp only [tryInvPkg, Option.mem_def, embedPkg] at h ⊢
  generalize htn : hcn.tryOrigN n' = on at h
  generalize htv : hcv.tryOrigV v' = ov at h
  match on, ov with
  | some n₀, some v₀ =>
    simp at h; obtain ⟨rfl, rfl⟩ := h
    show (hcn.origN n₀, hcv.origV v₀) = (n', v')
    rw [hcn.tryOrigN_some _ _ htn, hcv.tryOrigV_some _ _ htv]
  | some _, none => simp at h
  | none, _ => simp at h

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem tryInvPkg_inj :
    ∀ a a' (b : Package N V), b ∈ tryInvPkg a → b ∈ tryInvPkg a' → a = a' := by
  intro a a' b ha ha'
  exact (tryInvPkg_some ha).symm.trans (tryInvPkg_some ha')

def preimageS (S : Finset (Package N' V')) : Finset (Package N V) :=
  S.filterMap tryInvPkg tryInvPkg_inj

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem mem_preimageS {S : Finset (Package N' V')} {p : Package N V} :
    p ∈ preimageS S ↔ embedPkg p ∈ S := by
  simp only [preimageS, Finset.mem_filterMap]
  constructor
  · rintro ⟨p', hp', hinv⟩
    rw [tryInvPkg_some hinv]; exact hp'
  · intro hp
    exact ⟨embedPkg p, hp, tryInvPkg_embed p⟩

omit [DecidableEq N] [DecidableEq V] in
theorem embedPkg_mem_real {p : Package N V} {R_Γ : Real N V} {Γ : ConflictRel N V}
    (h : embedPkg p ∈ conflictReal R_Γ Γ) : p ∈ R_Γ := by
  simp only [conflictReal, embedSet, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at h
  rcases h with ⟨q, hqR, hqeq⟩ | ⟨a, _, hmem⟩
  · simp only [embedPkg, Prod.mk.injEq] at hqeq
    exact (Prod.ext (hcn.origN.injective hqeq.1) (hcv.origV.injective hqeq.2)) ▸ hqR
  · simp only [Finset.mem_insert, Finset.mem_singleton, embedPkg, Prod.mk.injEq] at hmem
    rcases hmem with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact absurd h1 (hcn.origN_ne_syntheticN _ _ _)

omit [DecidableEq N] [DecidableEq V] in
theorem conflict_soundness
    (R_Γ : Real N V) (Δ_Γ : DepRel N V) (Γ : ConflictRel N V)
    (r : Package N V)
    (S : Finset (Package N' V'))
    (hres : IsResolution (conflictReal R_Γ Γ) (conflictDeps Δ_Γ Γ) (embedPkg r) S) :
    IsConflictResolution R_Γ Δ_Γ Γ r (preimageS S) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- subset
    intro p hp
    rw [mem_preimageS] at hp
    exact embedPkg_mem_real (hres.subset hp)
  · -- root_mem
    rw [mem_preimageS]
    exact hres.root_mem
  · -- dep_closure
    intro p hp m vs hmem
    rw [mem_preimageS] at hp
    have hd : (embedPkg p, hcn.origN m, embedVS vs) ∈ conflictDeps Δ_Γ Γ := by
      simp only [conflictDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
      exact Or.inl (Or.inl ⟨⟨p, m, vs⟩, hmem, rfl⟩)
    obtain ⟨v', hv', hv'S⟩ := hres.dep_closure _ hp _ _ hd
    simp only [embedVS, Finset.mem_map] at hv'
    obtain ⟨v, hv, rfl⟩ := hv'
    exact ⟨v, hv, mem_preimageS.mpr hv'S⟩
  · -- version_unique
    intro n v v' hv hv'
    rw [mem_preimageS] at hv hv'
    exact hcv.origV.injective (hres.version_unique _ _ _ hv hv')
  · -- conflict_avoidance
    intro p hp n vs hg ⟨u, hu, humem⟩
    rw [mem_preimageS] at hp humem
    have hd1 : (embedPkg p, hcn.syntheticN n vs, {hcv.oneV}) ∈ conflictDeps Δ_Γ Γ := by
      simp only [conflictDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
      exact Or.inl (Or.inr ⟨⟨p, n, vs⟩, hg, rfl⟩)
    obtain ⟨v₁, hv₁mem, hv1S⟩ := hres.dep_closure _ hp _ _ hd1
    rw [Finset.mem_singleton.mp hv₁mem] at hv1S
    have hd2 : (embedPkg (n, u), hcn.syntheticN n vs, {hcv.zeroV}) ∈ conflictDeps Δ_Γ Γ := by
      simp only [conflictDeps, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
      right
      exact ⟨⟨p, n, vs⟩, hg, u, hu, rfl⟩
    obtain ⟨v₂, hv₂mem, hv2S⟩ := hres.dep_closure _ humem _ _ hd2
    rw [Finset.mem_singleton.mp hv₂mem] at hv2S
    exact absurd (hres.version_unique _ _ _ hv1S hv2S) hcv.oneV_ne_zeroV

end PackageCalculus.Conflict
