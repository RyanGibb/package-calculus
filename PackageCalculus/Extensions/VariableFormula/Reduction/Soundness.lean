import PackageCalculus.Extensions.VariableFormula.Reduction.Definition
import Mathlib

/-! # Variable-formula extension: soundness

Any core resolution of the variable-formula encoding induces a satisfying
assignment together with a valid variable-formula resolution. -/

namespace PackageCalculus.VarFormula

open Classical

variable {N : Type*} {V : Type*} {X : Type*} {Y : Type*}
variable {N' : Type*} {V' : Type*}
variable [DecidableEq N'] [DecidableEq V']
variable [hvn : HasVFNames N V X Y N'] [hvv : HasVFVersions V Y V']

omit [DecidableEq N'] [DecidableEq V'] in
private theorem embedPkg_injective :
    Function.Injective (embedPkg (X := X) (Y := Y) : Package N V → Package N' V') := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [embedPkg, Prod.mk.injEq] at h
  exact Prod.ext (hvn.origN.injective h.1) (hvv.origV.injective h.2)

private noncomputable def preimageS [DecidableEq N] [DecidableEq V]
    (S : Finset (Package N' V')) : Finset (Package N V) :=
  S.preimage (embedPkg (X := X) (Y := Y))
    (Set.InjOn.mono (Set.subset_univ _)
      (Function.Injective.injOn (embedPkg_injective (X := X) (Y := Y))))

omit [DecidableEq N'] [DecidableEq V'] in
private theorem mem_preimageS [DecidableEq N] [DecidableEq V]
    {S : Finset (Package N' V')} {p : Package N V} :
    p ∈ preimageS (X := X) (Y := Y) S ↔ embedPkg (X := X) (Y := Y) p ∈ S := by
  simp [preimageS, Finset.mem_preimage]

/-- Recover the variable assignment `σ` from a core resolution `S`: paper
spec is `σ = {(x, y) | (⟨x⟩, y) ∈ S}`. We pick `y` via choice; if no such
package exists in `S`, fall back to `Classical.arbitrary Y`. -/
noncomputable def extractAssignment [Nonempty Y]
    (S : Finset (Package N' V')) :
    X → Y :=
  fun x => if h : ∃ y, (hvn.varN x, hvv.varValV y) ∈ S
           then h.choose else Classical.arbitrary Y

omit [DecidableEq N'] [DecidableEq V'] in
private lemma extractAssignment_var [Nonempty Y]
    {R : Real N' V'}
    {Δ : DepRel N' V'}
    {r : Package N' V'}
    {S : Finset (Package N' V')}
    (hres : IsResolution R Δ r S)
    (x : X) (y' : Y)
    (hS : (hvn.varN x, hvv.varValV y') ∈ S) :
    (extractAssignment (N := N) (V := V) (X := X) (Y := Y) S) x = y' := by
  unfold extractAssignment
  have hex : ∃ y₀, (hvn.varN x, hvv.varValV y₀) ∈ S := ⟨y', hS⟩
  rw [dif_pos hex]
  exact hvv.varValV.injective (hres.version_unique _ _ _ hex.choose_spec hS)

private theorem witnessPackages_not_orig
    [LT Y] [DecidableEq Y] [DecidableRel (· < · : Y → Y → Prop)]
    (p : Package N' V') (ψ : Formula N V X Y) (n : N) (v : V') :
    (hvn.origN n, v) ∉ witnessPackages p ψ := by
  by_contra h_contra;
  induction' h : Formula.weight ψ using Nat.strong_induction_on with w hw generalizing ψ p;
  rcases ψ with ( _ | ⟨ ψ_L, ψ_R ⟩ | ⟨ ψ_L, ψ_R ⟩ | ⟨ x, ω, y ⟩ | ⟨ n, vs ⟩ );
  all_goals simp +decide [ witnessPackages ] at h_contra;
  · rcases h_contra with ( h_contra | h_contra );
    · exact hw _ ( by simp +decide [ Formula.weight ] at h ⊢; linarith ) _ _ h_contra rfl;
    · exact hw _ ( by rw [ show ( ψ_L.conj ψ_R ).weight = ψ_L.weight + ψ_R.weight + 2 from rfl ] at h; linarith ) _ _ h_contra rfl;
  · rcases h_contra with ( h_contra | h_contra );
    · exact hw _ ( by simp +decide [ Formula.weight ] at h ⊢; linarith ) _ _ h_contra rfl;
    · exact hw _ ( by simp +decide [ Formula.weight ] at h ⊢; linarith ) _ _ h_contra rfl;
  · rcases h_contra with ( h_contra | h_contra );
    · exact hw _ ( by simp +decide [ Formula.weight ] at h ⊢; linarith ) _ _ h_contra rfl;
    · exact hw _ ( by simp +decide [ Formula.weight ] at h ⊢; linarith ) _ _ h_contra rfl;
  · rcases h_contra with ( h_contra | h_contra );
    · exact hw _ ( by simp +decide [ Formula.weight ] at h ⊢; linarith ) _ _ h_contra rfl;
    · exact hw _ ( by simp +decide [ Formula.weight ] at h ⊢; linarith ) _ _ h_contra rfl;
  · exact hw _ ( by linarith [ show Formula.weight ‹_› < w from by linarith [ show Formula.weight ( Formula.neg ( Formula.neg ‹_› ) ) = 3 * ( Formula.weight ( Formula.neg ‹_› ) + 1 ) from rfl, show Formula.weight ( Formula.neg ‹_› ) = 3 * ( Formula.weight ‹_› + 1 ) from rfl ] ] ) _ _ h_contra rfl

private theorem embedPkg_mem_vfReal
    [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
    [LT Y] [DecidableRel (· < · : Y → Y → Prop)] [Fintype X]
    (Y_x : X → Finset Y)
    {p : Package N V} {R_Ψ : Real N V} {Δ_Ψ : VFDepRel N V X Y}
    (h : embedPkg (X := X) (Y := Y) p ∈ vfReal Y_x R_Ψ Δ_Ψ) : p ∈ R_Ψ := by
  unfold vfReal at h; simp_all +decide [ Finset.mem_biUnion, Finset.mem_image, Function.Injective.eq_iff ( show Function.Injective ( embedPkg : Package N V → Package N' V' ) from embedPkg_injective ) ] ;
  rcases h with ( h | ⟨ a, b, c, h₁, h₂ ⟩ | ⟨ a, b, h₁, h₂ ⟩ ) <;> simp_all +decide [ embedPkg ];
  exact False.elim ( witnessPackages_not_orig _ _ _ _ h₂ )

private def encode_satisfies [DecidableEq N] [DecidableEq V]
    [DecidableEq X] [DecidableEq Y]
    [LT Y] [DecidableRel (· < · : Y → Y → Prop)] [Nonempty Y]
    {R : Real N' V'}
    {Δ : DepRel N' V'}
    {r : Package N' V'}
    {S : Finset (Package N' V')}
    (hres : IsResolution R Δ r S)
    (Y_x : X → Finset Y)
    (q : Package N' V')
    (ψ : Formula N V X Y)
    (henc : ∀ d, d ∈ encodeNNF Y_x q ψ → d ∈ Δ) (hq : q ∈ S) :
    ψ.satisfies
      (preimageS (X := X) (Y := Y) S)
      (extractAssignment (N := N) (V := V) (X := X) (Y := Y) S) := by
  match ψ with
  | .dep n vs =>
    simp only [encodeNNF] at henc
    have hd := henc _ (Finset.mem_singleton.mpr rfl)
    obtain ⟨w, hw, hwS⟩ := hres.dep_closure _ hq _ _ hd
    simp only [Finset.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨v, hv, mem_preimageS.mpr hwS⟩
  | .conj ψ_L ψ_R =>
    simp only [encodeNNF] at henc
    exact ⟨encode_satisfies hres Y_x q ψ_L
            (fun d hd => henc d (Finset.mem_union.mpr (Or.inl hd))) hq,
           encode_satisfies hres Y_x q ψ_R
            (fun d hd => henc d (Finset.mem_union.mpr (Or.inr hd))) hq⟩
  | .disj ψ_L ψ_R =>
    simp only [encodeNNF] at henc
    have hd : (q, hvn.disjunctN ψ_L ψ_R,
        ({hvv.zeroV, hvv.oneV} : Finset _)) ∈ Δ :=
      henc _ (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_singleton.mpr rfl)))))
    obtain ⟨w, hw, hwS⟩ := hres.dep_closure _ hq _ _ hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · left
      exact encode_satisfies hres Y_x _ ψ_L
        (fun d hd' => henc d (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hd'))))) hwS
    · right
      exact encode_satisfies hres Y_x _ ψ_R
        (fun d hd' => henc d (Finset.mem_union.mpr (Or.inr hd'))) hwS
  | .varCmp x ω y =>
    simp only [encodeNNF] at henc
    have hd := henc _ (Finset.mem_singleton.mpr rfl)
    obtain ⟨w, hw, hwS⟩ := hres.dep_closure _ hq _ _ hd
    obtain ⟨y', rfl, _, heval⟩ := mem_cmpVersionSet' hw
    simp only [Formula.satisfies]
    rw [extractAssignment_var hres x y' hwS]
    exact heval
  | .neg (.dep n vs) =>
    simp only [encodeNNF] at henc
    have hd : (q, hvn.syntheticN n vs,
        ({hvv.oneV} : Finset V')) ∈ Δ :=
      henc _ (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton.mpr rfl)))
    obtain ⟨w, hw, hwS⟩ := hres.dep_closure _ hq _ _ hd
    simp only [Finset.mem_singleton] at hw; subst hw
    intro ⟨v, hv, hvS⟩
    rw [mem_preimageS] at hvS
    have hd2 : ((hvn.origN n, hvv.origV v),
        hvn.syntheticN n vs, ({hvv.zeroV} : Finset V')) ∈ Δ :=
      henc _ (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨v, hv, rfl⟩)))
    obtain ⟨w2, hw2, hw2S⟩ := hres.dep_closure _ hvS _ _ hd2
    simp only [Finset.mem_singleton] at hw2; subst hw2
    exact absurd (hres.version_unique _ _ _ hwS hw2S) hvv.oneV_ne_zeroV
  | .neg (.varCmp x ω y) =>
    show ¬ Formula.satisfies (preimageS S) (extractAssignment S) (.varCmp x ω y)
    have key : encodeNNF (hvn := hvn) (hvv := hvv) Y_x q
        (Formula.neg (Formula.varCmp x ω y) : Formula N V X Y) =
        encodeNNF (hvn := hvn) (hvv := hvv) Y_x q
        (Formula.varCmp x (CmpOp.complement ω) y : Formula N V X Y) := by
      simp [encodeNNF]
    have h := encode_satisfies hres Y_x q (Formula.varCmp x (CmpOp.complement ω) y)
      (fun d hd => henc d (key ▸ hd)) hq
    simp only [Formula.satisfies] at h ⊢
    exact (complement_eval ω _ _).mp h
  | .neg (.conj ψ_L ψ_R) =>
    have key : encodeNNF Y_x q (.neg (.conj ψ_L ψ_R)) =
        encodeNNF Y_x q (.disj (.neg ψ_L) (.neg ψ_R)) := by
      simp [encodeNNF]
    have h := encode_satisfies hres Y_x q (.disj (.neg ψ_L) (.neg ψ_R))
      (fun d hd => henc d (key ▸ hd)) hq
    simp only [Formula.satisfies] at h ⊢
    exact not_and_or.mpr h
  | .neg (.disj ψ_L ψ_R) =>
    have key : encodeNNF Y_x q (.neg (.disj ψ_L ψ_R)) =
        encodeNNF Y_x q (.conj (.neg ψ_L) (.neg ψ_R)) := by
      simp [encodeNNF]
    have h := encode_satisfies hres Y_x q (.conj (.neg ψ_L) (.neg ψ_R))
      (fun d hd => henc d (key ▸ hd)) hq
    simp only [Formula.satisfies] at h ⊢
    exact not_or.mpr h
  | .neg (.neg ψ') =>
    have key : encodeNNF Y_x q (.neg (.neg ψ')) = encodeNNF Y_x q ψ' := by
      simp [encodeNNF]
    have h := encode_satisfies hres Y_x q ψ' (fun d hd => henc d (key ▸ hd)) hq
    simp only [Formula.satisfies]
    exact not_not_intro h
  termination_by ψ.weight
  decreasing_by all_goals simp only [Formula.weight]; omega

-- Paper Thm 4.6.4 (Variable Formula Reduction Soundness).
theorem variable_formula_soundness
    [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
    [LT Y] [DecidableRel (· < · : Y → Y → Prop)] [Fintype X] [Nonempty Y]
    (Y_x : X → Finset Y)
    (R_Ψ : Real N V) (Δ_Ψ : VFDepRel N V X Y)
    (r : Package N V)
    (S : Finset (Package N' V'))
    (hres : IsResolution (vfReal Y_x R_Ψ Δ_Ψ) (vfDeps Y_x Δ_Ψ)
      (embedPkg (X := X) (Y := Y) r) S) :
    IsVFResolution R_Ψ Δ_Ψ r (preimageS (X := X) (Y := Y) S)
      (extractAssignment (N := N) (V := V) (X := X) (Y := Y) S) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- subset
    intro p hp
    rw [mem_preimageS] at hp
    exact embedPkg_mem_vfReal Y_x (hres.subset hp)
  · -- root_mem
    exact mem_preimageS.mpr hres.root_mem
  · -- formula_closure
    intro p hp ψ hdep
    rw [mem_preimageS] at hp
    have henc : ∀ d, d ∈ encodeNNF Y_x (embedPkg (X := X) (Y := Y) p) ψ →
        d ∈ vfDeps Y_x Δ_Ψ := by
      intro d hd
      simp only [vfDeps, encode, Finset.mem_biUnion]
      exact ⟨⟨p, ψ⟩, hdep, hd⟩
    exact encode_satisfies hres Y_x (embedPkg (X := X) (Y := Y) p) ψ henc hp
  · -- version_unique
    intro n v v' hv hv'
    rw [mem_preimageS] at hv hv'
    exact hvv.origV.injective (hres.version_unique _ _ _ hv hv')

end PackageCalculus.VarFormula