import PackageCalculus.Extensions.Feature.Lifting.Definition

namespace PackageCalculus.Feature

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {F : Type*} [DecidableEq F] [Fintype F]
variable {N' : Type*} [DecidableEq N'] [hfn : HasFeatureNames N F N']

/-! ## Lifting soundness & completeness -/

theorem liftResolution_soundness
    (R_f : Real N V) (support : Support N V F)
    (Δ_f : FeatDepRel N V F) (Δ_a : AddlDepRel N V F)
    (r : Package N V) (S' : Finset (Package N' V))
    (hres : IsResolution (featureReal R_f support) (featureDeps R_f support Δ_f Δ_a)
      (embedPkg F r) S')
    (hroot_no_support : ∀ f, (r, f) ∉ support) :
    IsFeatureResolution R_f support Δ_f Δ_a r (liftResolution S') := by
  have h := feature_soundness R_f support Δ_f Δ_a r S' hres hroot_no_support
  -- soundnessWitness and liftResolution agree extensionally
  suffices heq : liftResolution S' = soundnessWitness S' by rw [heq]; exact h
  simp only [liftResolution, soundnessWitness]
  congr 1
  ext ⟨n, v⟩
  simp only [Finset.mem_filterMap, Finset.mem_preimage, embedPkg]
  constructor
  · rintro ⟨p', hp', hinv⟩
    have heq := tryInvPkg_some hinv
    simp only [embedPkg] at heq
    exact heq ▸ hp'
  · intro hp
    exact ⟨(hfn.origN n, v), hp, by simp [tryInvPkg, hfn.tryOrigN_origN]⟩


end PackageCalculus.Feature
