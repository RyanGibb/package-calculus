import PackageCalculus.Extensions.Feature.Lifting.Definition

namespace PackageCalculus.Feature

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {F : Type*} [DecidableEq F] [Fintype F]
variable {N' : Type*} [DecidableEq N'] [hfn : HasFeatureNames N F N']

theorem liftResolution_completenessWitness
    (S_f : Finset (Package N V × Finset F))
    (hfu : ∀ n v v' fs fs', ((n, v), fs) ∈ S_f → ((n, v'), fs') ∈ S_f → fs = fs') :
    liftResolution (hfn := hfn) (completenessWitness S_f) = S_f := by
  ext p;
  constructor <;> intro hp;
  · obtain ⟨ n, v, h₁, rfl ⟩ := liftResolution_elim hp;
    unfold completenessWitness at *;
    simp +zetaDelta at *;
    convert h₁.choose_spec using 1;
    refine' congr_arg _ ( Finset.ext fun f => _ );
    simp +decide ;
    constructor;
    · rintro ⟨ a, b, hb, x, hx, hx' ⟩;
      have := hfn.featuredN_injective hx';
      grind;
    · exact fun hf => ⟨ n, _, h₁.choose_spec, f, hf, rfl ⟩;
  · convert mem_liftResolution' _;
    · ext f; simp [completenessWitness];
      constructor;
      · exact fun hf => ⟨ p.1.1, p.2, hp, f, hf, rfl ⟩;
      · rintro ⟨ a, b, hb, x, hx, h ⟩;
        have := hfn.featuredN_injective h;
        grind;
    · exact Finset.mem_union_left _ ( Finset.mem_image_of_mem _ hp )

theorem liftResolution_completeness
    (R_f : Real N V) (support : Support N V F)
    (Δ_f : FeatDepRel N V F) (Δ_a : AddlDepRel N V F)
    (r : Package N V)
    (S_f : Finset (Package N V × Finset F))
    (hres : IsFeatureResolution R_f support Δ_f Δ_a r S_f) :
    ∃ S', IsResolution (featureReal R_f support) (featureDeps R_f support Δ_f Δ_a)
      (embedPkg F r) S' ∧ liftResolution S' = S_f :=
  ⟨completenessWitness S_f, feature_completeness R_f support Δ_f Δ_a r S_f hres,
   liftResolution_completenessWitness S_f hres.feature_unification⟩


end PackageCalculus.Feature