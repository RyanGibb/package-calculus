import PackageCalculus.Extensions.Concurrent.Definition
import PackageCalculus.Extensions.Feature.Reduction.Definition

/-! # Feature-concurrent composition: shared types

Flattened name and version types `N_FC`, `V_FC` that combine the concurrent
and feature embeddings, together with the typeclasses that introduce shared
and per-feature intermediate constructors. -/

namespace PackageCalculus.Composition

open Function

variable {N F V G : Type*}

/-- Flattened name type for the joint Concurrent Feature reduction.

    The first six constructors (`granularOrig`, `granularFeatured`, and the four
    `intermediate*` variants) provide the `Concurrent.HasConcurrentNames` instance for the
    feature-level name type. The Concurrent Feature reduction itself does **not** use the
    `intermediate*` constructors; they are present only so the underlying typeclass instance
    can be defined. The new shared intermediate is `concurrentFeatureIntermediate p_n p_v n`,
    corresponding to the paper's `⟨(p_n, p_v), n⟩`. It is parameterised by the depender's
    base name, its full version, and the dependee's base name. -/
inductive FCName (N F V G : Type*) where
  | granularOrig : N → G → FCName N F V G
  | granularFeatured : N → F → G → FCName N F V G
  | intermediateOrigOrig : N → V → N → FCName N F V G
  | intermediateOrigFeatured : N → V → N → F → FCName N F V G
  | intermediateFeaturedOrig : N → F → V → N → FCName N F V G
  | intermediateFeaturedFeatured : N → F → V → N → F → FCName N F V G
  /-- Shared intermediate `⟨(p_n, p_v), n⟩` for a Δ_f or Δ_a dep on the base
      depender--dependee pair `((p_n, p_v), n)`. -/
  | concurrentFeatureIntermediate : N → V → N → FCName N F V G
  /-- Per-feature secondary intermediate `⟨(p_n, p_v), n, f⟩` for a Δ_f dep, used to route the
      depender's orig package to each `f ∈ fs` feature granular of the dependee. -/
  | concurrentFeatureIntermediate_f : N → V → N → F → FCName N F V G
  /-- Per-feature secondary intermediate `⟨(p_n, p_v), f, n, f'⟩` for a Δ_a dep, used to
      route the depender's featured (by `f`) package to each `f' ∈ fs` feature granular of the
      dependee. -/
  | concurrentFeatureIntermediate_a : N → V → F → N → F → FCName N F V G

instance : Concurrent.HasConcurrentNames (Feature.FeatureName N F) V G (FCName N F V G) where
  granularN := fun fn g => match fn with
    | .orig n => .granularOrig n g
    | .featured n f => .granularFeatured n f g
  intermediateN := fun fn v fm => match fn, fm with
    | .orig n, .orig m => .intermediateOrigOrig n v m
    | .orig n, .featured m f => .intermediateOrigFeatured n v m f
    | .featured n f, .orig m => .intermediateFeaturedOrig n f v m
    | .featured n f, .featured m f' => .intermediateFeaturedFeatured n f v m f'
  granularN_injective := by
    intro fn₁ fn₂ g₁ g₂ h
    cases fn₁ with
    | orig n₁ =>
      cases fn₂ with
      | orig n₂ =>
        have h' := FCName.granularOrig.inj h
        exact ⟨congrArg Feature.FeatureName.orig h'.1, h'.2⟩
      | featured n₂ f₂ => exact nomatch h
    | featured n₁ f₁ =>
      cases fn₂ with
      | orig n₂ => exact nomatch h
      | featured n₂ f₂ =>
        have h' := FCName.granularFeatured.inj h
        exact ⟨h'.1 ▸ h'.2.1 ▸ rfl, h'.2.2⟩
  intermediateN_injective := by
    intro fn₁ v₁ fm₁ fn₂ v₂ fm₂ h
    cases fn₁ with
    | orig n₁ =>
      cases fn₂ with
      | orig n₂ =>
        cases fm₁ with
        | orig m₁ =>
          cases fm₂ with
          | orig m₂ =>
            have h' := FCName.intermediateOrigOrig.inj h
            exact ⟨congrArg Feature.FeatureName.orig h'.1, h'.2.1,
                   congrArg Feature.FeatureName.orig h'.2.2⟩
          | featured m₂ f₂ => exact nomatch h
        | featured m₁ f₁ =>
          cases fm₂ with
          | orig m₂ => exact nomatch h
          | featured m₂ f₂ =>
            have h' := FCName.intermediateOrigFeatured.inj h
            exact ⟨congrArg Feature.FeatureName.orig h'.1, h'.2.1, h'.2.2.1 ▸ h'.2.2.2 ▸ rfl⟩
      | featured n₂ f₂ =>
        cases fm₁ with
        | orig m₁ =>
          cases fm₂ with
          | orig m₂ => exact nomatch h
          | featured m₂ f₂' => exact nomatch h
        | featured m₁ f₁ =>
          cases fm₂ with
          | orig m₂ => exact nomatch h
          | featured m₂ f₂' => exact nomatch h
    | featured n₁ f₁ =>
      cases fn₂ with
      | orig n₂ =>
        cases fm₁ with
        | orig m₁ =>
          cases fm₂ with
          | orig m₂ => exact nomatch h
          | featured m₂ f₂ => exact nomatch h
        | featured m₁ f₁' =>
          cases fm₂ with
          | orig m₂ => exact nomatch h
          | featured m₂ f₂ => exact nomatch h
      | featured n₂ f₂ =>
        cases fm₁ with
        | orig m₁ =>
          cases fm₂ with
          | orig m₂ =>
            have h' := FCName.intermediateFeaturedOrig.inj h
            exact ⟨h'.1 ▸ h'.2.1 ▸ rfl, h'.2.2.1, congrArg Feature.FeatureName.orig h'.2.2.2⟩
          | featured m₂ f₂' => exact nomatch h
        | featured m₁ f₁' =>
          cases fm₂ with
          | orig m₂ => exact nomatch h
          | featured m₂ f₂' =>
            have h' := FCName.intermediateFeaturedFeatured.inj h
            exact ⟨h'.1 ▸ h'.2.1 ▸ rfl, h'.2.2.1, h'.2.2.2.1 ▸ h'.2.2.2.2 ▸ rfl⟩
  granularN_ne_intermediateN := fun fn g fn' v fm => by
    cases fn <;> cases fn' <;> cases fm <;> nofun
  intermediateN_ne_granularN := fun fn v fm fn' g => by
    cases fn <;> cases fn' <;> cases fm <;> nofun
  tryGranularN := fun
    | .granularOrig n g => some (.orig n, g)
    | .granularFeatured n f g => some (.featured n f, g)
    | _ => none
  tryGranularN_granularN := fun fn g => by cases fn <;> rfl
  tryGranularN_some := fun n' p h => by
    cases n' with
    | granularOrig n g => simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
    | granularFeatured n f g => simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
    | _ => simp at h

/-- Typeclass providing the shared intermediate constructor used by the joint Concurrent
    Feature reduction. The constructor takes the depender's base name, its full version,
    and the dependee's base name. It must be distinct from all `granularN` and
    `intermediateN` constructors of the underlying `HasConcurrentNames` instance. -/
class HasConcurrentFeatureIntermediate (N V F G : Type*) (N' : outParam Type*)
    [hcnm : Concurrent.HasConcurrentNames (Feature.FeatureName N F) V G N'] where
  /-- Shared intermediate `⟨(p_n, p_v), n⟩`. -/
  cfIntermediateN : N → V → N → N'
  /-- Per-feature secondary intermediate `⟨(p_n, p_v), n, f⟩` for Δ_f deps. -/
  cfIntermediateN_f : N → V → N → F → N'
  /-- Per-feature secondary intermediate `⟨(p_n, p_v), f, n, f'⟩` for Δ_a deps. -/
  cfIntermediateN_a : N → V → F → N → F → N'
  cfIntermediateN_injective :
    ∀ p_n₁ p_v₁ n₁ p_n₂ p_v₂ n₂,
      cfIntermediateN p_n₁ p_v₁ n₁ = cfIntermediateN p_n₂ p_v₂ n₂ →
      p_n₁ = p_n₂ ∧ p_v₁ = p_v₂ ∧ n₁ = n₂
  cfIntermediateN_f_injective :
    ∀ p_n₁ p_v₁ n₁ f₁ p_n₂ p_v₂ n₂ f₂,
      cfIntermediateN_f p_n₁ p_v₁ n₁ f₁ = cfIntermediateN_f p_n₂ p_v₂ n₂ f₂ →
      p_n₁ = p_n₂ ∧ p_v₁ = p_v₂ ∧ n₁ = n₂ ∧ f₁ = f₂
  cfIntermediateN_a_injective :
    ∀ p_n₁ p_v₁ f₁ n₁ f'₁ p_n₂ p_v₂ f₂ n₂ f'₂,
      cfIntermediateN_a p_n₁ p_v₁ f₁ n₁ f'₁ = cfIntermediateN_a p_n₂ p_v₂ f₂ n₂ f'₂ →
      p_n₁ = p_n₂ ∧ p_v₁ = p_v₂ ∧ f₁ = f₂ ∧ n₁ = n₂ ∧ f'₁ = f'₂
  cfIntermediateN_ne_granularN :
    ∀ p_n p_v n fn g, cfIntermediateN p_n p_v n ≠ hcnm.granularN fn g
  cfIntermediateN_ne_intermediateN :
    ∀ p_n p_v n fn v fm, cfIntermediateN p_n p_v n ≠ hcnm.intermediateN fn v fm
  cfIntermediateN_f_ne_granularN :
    ∀ p_n p_v n f fn g, cfIntermediateN_f p_n p_v n f ≠ hcnm.granularN fn g
  cfIntermediateN_f_ne_intermediateN :
    ∀ p_n p_v n f fn v fm, cfIntermediateN_f p_n p_v n f ≠ hcnm.intermediateN fn v fm
  cfIntermediateN_f_ne_cfIntermediateN :
    ∀ p_n p_v n f p_n' p_v' n', cfIntermediateN_f p_n p_v n f ≠ cfIntermediateN p_n' p_v' n'
  cfIntermediateN_a_ne_granularN :
    ∀ p_n p_v f n f' fn g, cfIntermediateN_a p_n p_v f n f' ≠ hcnm.granularN fn g
  cfIntermediateN_a_ne_intermediateN :
    ∀ p_n p_v f n f' fn v fm, cfIntermediateN_a p_n p_v f n f' ≠ hcnm.intermediateN fn v fm
  cfIntermediateN_a_ne_cfIntermediateN :
    ∀ p_n p_v f n f' p_n' p_v' n', cfIntermediateN_a p_n p_v f n f' ≠ cfIntermediateN p_n' p_v' n'
  cfIntermediateN_a_ne_cfIntermediateN_f :
    ∀ p_n p_v f n f' p_n' p_v' n' f'', cfIntermediateN_a p_n p_v f n f' ≠ cfIntermediateN_f p_n' p_v' n' f''

attribute [simp]
  HasConcurrentFeatureIntermediate.cfIntermediateN_ne_granularN
  HasConcurrentFeatureIntermediate.cfIntermediateN_ne_intermediateN
  HasConcurrentFeatureIntermediate.cfIntermediateN_f_ne_granularN
  HasConcurrentFeatureIntermediate.cfIntermediateN_f_ne_intermediateN
  HasConcurrentFeatureIntermediate.cfIntermediateN_f_ne_cfIntermediateN
  HasConcurrentFeatureIntermediate.cfIntermediateN_a_ne_granularN
  HasConcurrentFeatureIntermediate.cfIntermediateN_a_ne_intermediateN
  HasConcurrentFeatureIntermediate.cfIntermediateN_a_ne_cfIntermediateN
  HasConcurrentFeatureIntermediate.cfIntermediateN_a_ne_cfIntermediateN_f

instance : HasConcurrentFeatureIntermediate N V F G (FCName N F V G) where
  cfIntermediateN := fun p_n p_v n => .concurrentFeatureIntermediate p_n p_v n
  cfIntermediateN_f := fun p_n p_v n f => .concurrentFeatureIntermediate_f p_n p_v n f
  cfIntermediateN_a := fun p_n p_v f n f' => .concurrentFeatureIntermediate_a p_n p_v f n f'
  cfIntermediateN_injective := by
    intro p_n₁ p_v₁ n₁ p_n₂ p_v₂ n₂ h
    have h' := FCName.concurrentFeatureIntermediate.inj h
    exact ⟨h'.1, h'.2.1, h'.2.2⟩
  cfIntermediateN_f_injective := by
    intro p_n₁ p_v₁ n₁ f₁ p_n₂ p_v₂ n₂ f₂ h
    have h' := FCName.concurrentFeatureIntermediate_f.inj h
    exact ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2⟩
  cfIntermediateN_a_injective := by
    intro p_n₁ p_v₁ f₁ n₁ f'₁ p_n₂ p_v₂ f₂ n₂ f'₂ h
    have h' := FCName.concurrentFeatureIntermediate_a.inj h
    exact ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩
  cfIntermediateN_ne_granularN := by
    intro p_n p_v n fn g; cases fn <;> nofun
  cfIntermediateN_ne_intermediateN := by
    intro p_n p_v n fn v fm; cases fn <;> cases fm <;> nofun
  cfIntermediateN_f_ne_granularN := by
    intro p_n p_v n f fn g; cases fn <;> nofun
  cfIntermediateN_f_ne_intermediateN := by
    intro p_n p_v n f fn v fm; cases fn <;> cases fm <;> nofun
  cfIntermediateN_f_ne_cfIntermediateN := by
    intro p_n p_v n f p_n' p_v' n'; nofun
  cfIntermediateN_a_ne_granularN := by
    intro p_n p_v f n f' fn g; cases fn <;> nofun
  cfIntermediateN_a_ne_intermediateN := by
    intro p_n p_v f n f' fn v fm; cases fn <;> cases fm <;> nofun
  cfIntermediateN_a_ne_cfIntermediateN := by
    intro p_n p_v f n f' p_n' p_v' n'; nofun
  cfIntermediateN_a_ne_cfIntermediateN_f := by
    intro p_n p_v f n f' p_n' p_v' n' f''; nofun

end PackageCalculus.Composition
