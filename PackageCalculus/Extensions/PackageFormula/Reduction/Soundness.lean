import PackageCalculus.Extensions.PackageFormula.Reduction.Definition
import Mathlib.Data.Finset.Preimage

/-! # Package-formula extension: soundness

Any core resolution of the formula encoding induces a package-formula
resolution that satisfies the original formulae. -/

namespace PackageCalculus.PkgFormula

open Classical

variable {N : Type*} {V : Type*} {N' : Type*} {V' : Type*}
variable [DecidableEq N'] [DecidableEq V']
variable [hpn : HasPFNames N V N'] [hpv : Conflict.HasConflictVersions V V']

omit [DecidableEq N'] [DecidableEq V'] in
private theorem embedPkg_injective :
    Function.Injective (embedPkg : Package N V → Package N' V') := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [embedPkg, Prod.mk.injEq] at h
  exact Prod.ext (hpn.origN.injective h.1) (hpv.origV.injective h.2)

private noncomputable def preimageS [DecidableEq N] [DecidableEq V]
    (S : Finset (Package N' V')) : Finset (Package N V) :=
  S.preimage embedPkg (Set.InjOn.mono (Set.subset_univ _)
    (Function.Injective.injOn embedPkg_injective))

omit [DecidableEq N'] [DecidableEq V'] in
private theorem mem_preimageS [DecidableEq N] [DecidableEq V]
    {S : Finset (Package N' V')} {p : Package N V} :
    p ∈ preimageS S ↔ embedPkg p ∈ S := by
  simp [preimageS, Finset.mem_preimage]

theorem witnessPackages_not_orig
    (p : Package N' V') (ψ : Formula N V) (n : N) (v : V') :
    (hpn.origN n, v) ∉ witnessPackages p ψ := by
  match ψ with
  | .dep _ _ => simp [witnessPackages]
  | .conj ψ_L ψ_R =>
    simp only [witnessPackages, Finset.mem_union]
    push_neg
    exact ⟨witnessPackages_not_orig p ψ_L n v, witnessPackages_not_orig p ψ_R n v⟩
  | .disj ψ_L ψ_R =>
    simp only [witnessPackages, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    push_neg
    exact ⟨⟨⟨fun h => absurd h (hpn.origN_ne_disjunctN _ _ _),
            fun h => absurd h (hpn.origN_ne_disjunctN _ _ _)⟩,
           witnessPackages_not_orig _ ψ_L n v⟩,
           witnessPackages_not_orig _ ψ_R n v⟩
  | .neg (.dep n' vs) =>
    simp only [witnessPackages, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    push_neg
    exact ⟨fun h => absurd h (hpn.origN_ne_syntheticN _ _ _),
           fun h => absurd h (hpn.origN_ne_syntheticN _ _ _)⟩
  | .neg (.conj ψ_L ψ_R) =>
    have key : witnessPackages p (.neg (.conj ψ_L ψ_R)) =
        witnessPackages p (.disj (.neg ψ_L) (.neg ψ_R)) := by simp [witnessPackages]
    rw [key]; exact witnessPackages_not_orig p (.disj (.neg ψ_L) (.neg ψ_R)) n v
  | .neg (.disj ψ_L ψ_R) =>
    have key : witnessPackages p (.neg (.disj ψ_L ψ_R)) =
        witnessPackages p (.conj (.neg ψ_L) (.neg ψ_R)) := by simp [witnessPackages]
    rw [key]; exact witnessPackages_not_orig p (.conj (.neg ψ_L) (.neg ψ_R)) n v
  | .neg (.neg ψ') =>
    have key : witnessPackages p (.neg (.neg ψ')) = witnessPackages p ψ' := by
      simp [witnessPackages]
    rw [key]; exact witnessPackages_not_orig p ψ' n v
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

private theorem embedPkg_mem_pfReal [DecidableEq N] [DecidableEq V]
    {p : Package N V} {R_Ψ : Real N V} {Δ_Ψ : PFDepRel N V}
    (h : embedPkg p ∈ pfReal R_Ψ Δ_Ψ) : p ∈ R_Ψ := by
  simp only [pfReal, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at h
  rcases h with ⟨q, hqR, hqeq⟩ | ⟨a, haΔ, hmem⟩
  · have := embedPkg_injective hqeq; subst this; exact hqR
  · exfalso
    exact witnessPackages_not_orig (embedPkg a.1) a.2 p.1 (hpv.origV p.2) hmem

private def encode_satisfies [DecidableEq N] [DecidableEq V]
    {R : Real N' V'}
    {Δ : DepRel N' V'}
    {r : Package N' V'}
    {S : Finset (Package N' V')}
    (hres : IsResolution R Δ r S)
    (q : Package N' V')
    (ψ : Formula N V)
    (henc : ∀ d, d ∈ encodeNNF q ψ → d ∈ Δ) (hq : q ∈ S) :
    (preimageS S) ⊨ ψ := by
  match ψ with
  | .dep n vs =>
    simp only [encodeNNF] at henc
    have hd := henc _ (Finset.mem_singleton.mpr rfl)
    obtain ⟨w, hw, hwS⟩ := hres.dep_closure _ hq _ _ hd
    rw [embedVS, Finset.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨v, hv, mem_preimageS.mpr hwS⟩
  | .conj ψ_L ψ_R =>
    simp only [encodeNNF] at henc
    exact ⟨encode_satisfies hres q ψ_L
            (fun d hd => henc d (Finset.mem_union.mpr (Or.inl hd))) hq,
           encode_satisfies hres q ψ_R
            (fun d hd => henc d (Finset.mem_union.mpr (Or.inr hd))) hq⟩
  | .disj ψ_L ψ_R =>
    simp only [encodeNNF] at henc
    have hd : (q, hpn.disjunctN ψ_L ψ_R,
        ({hpv.zeroV, hpv.oneV} : Finset _)) ∈ Δ :=
      henc _ (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_singleton.mpr rfl)))))
    obtain ⟨w, hw, hwS⟩ := hres.dep_closure _ hq _ _ hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · left
      exact encode_satisfies hres _ ψ_L
        (fun d hd' => henc d (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hd'))))) hwS
    · right
      exact encode_satisfies hres _ ψ_R
        (fun d hd' => henc d (Finset.mem_union.mpr (Or.inr hd'))) hwS
  | .neg (.dep n vs) =>
    simp only [encodeNNF] at henc
    have hd : (q, hpn.syntheticN n vs,
        ({hpv.oneV} : Finset V')) ∈ Δ :=
      henc _ (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton.mpr rfl)))
    obtain ⟨w, hw, hwS⟩ := hres.dep_closure _ hq _ _ hd
    simp only [Finset.mem_singleton] at hw; subst hw
    intro ⟨v, hv, hvS⟩
    rw [mem_preimageS] at hvS
    have hd2 : ((hpn.origN n, hpv.origV v),
        hpn.syntheticN n vs, ({hpv.zeroV} : Finset V')) ∈ Δ :=
      henc _ (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨v, hv, rfl⟩)))
    obtain ⟨w2, hw2, hw2S⟩ := hres.dep_closure _ hvS _ _ hd2
    simp only [Finset.mem_singleton] at hw2; subst hw2
    exact absurd (hres.version_unique _ _ _ hwS hw2S) hpv.oneV_ne_zeroV
  | .neg (.conj ψ_L ψ_R) =>
    have key : encodeNNF q (.neg (.conj ψ_L ψ_R)) = encodeNNF q (.disj (.neg ψ_L) (.neg ψ_R)) := by
      simp [encodeNNF]
    have h := encode_satisfies hres q (.disj (.neg ψ_L) (.neg ψ_R))
      (fun d hd => henc d (key ▸ hd)) hq
    simp only [Formula.satisfies] at h ⊢
    exact not_and_or.mpr h
  | .neg (.disj ψ_L ψ_R) =>
    have key : encodeNNF q (.neg (.disj ψ_L ψ_R)) = encodeNNF q (.conj (.neg ψ_L) (.neg ψ_R)) := by
      simp [encodeNNF]
    have h := encode_satisfies hres q (.conj (.neg ψ_L) (.neg ψ_R))
      (fun d hd => henc d (key ▸ hd)) hq
    simp only [Formula.satisfies] at h ⊢
    exact not_or.mpr h
  | .neg (.neg ψ') =>
    have key : encodeNNF q (.neg (.neg ψ')) = encodeNNF q ψ' := by
      simp [encodeNNF]
    have h := encode_satisfies hres q ψ' (fun d hd => henc d (key ▸ hd)) hq
    simp only [Formula.satisfies]
    exact not_not_intro h
termination_by ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

-- Paper Thm 4.5.5 (Package Formula Reduction Soundness).
theorem package_formula_soundness [DecidableEq N] [DecidableEq V]
    (R_Ψ : Real N V) (Δ_Ψ : PFDepRel N V)
    (r : Package N V)
    (S : Finset (Package N' V'))
    (hres : IsResolution (pfReal R_Ψ Δ_Ψ) (pfDeps Δ_Ψ) (embedPkg r) S) :
    IsPFResolution R_Ψ Δ_Ψ r (preimageS S) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- subset: orig-named packages in pfReal come only from R_Ψ
    intro p hp
    rw [mem_preimageS] at hp
    exact embedPkg_mem_pfReal (hres.subset hp)
  · -- root_mem
    exact mem_preimageS.mpr hres.root_mem
  · -- formula_closure: by encode_satisfies
    intro p hp ψ hdep
    rw [mem_preimageS] at hp
    have henc : ∀ d, d ∈ encodeNNF (embedPkg p) ψ → d ∈ pfDeps Δ_Ψ := by
      intro d hd
      simp only [pfDeps, Finset.mem_biUnion]
      exact ⟨⟨p, ψ⟩, hdep, hd⟩
    exact encode_satisfies hres (embedPkg p) ψ henc hp
  · -- version_unique
    intro n v v' hv hv'
    rw [mem_preimageS] at hv hv'
    exact hpv.origV.injective (hres.version_unique _ _ _ hv hv')

end PackageCalculus.PkgFormula
