import PackageCalculus.Extensions.Feature.Definition
import Mathlib.Data.Finset.Union

/-! # Feature extension: reduction

Encodes feature flags into the core calculus by splitting each package name
into an *origin* variant and per-feature variants, and translating feature
constraints into core dependencies. -/

namespace PackageCalculus.Feature

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {F : Type*} [DecidableEq F]

inductive FeatureName (N F : Type*) where
  | orig : N → FeatureName N F
  | featured : N → F → FeatureName N F
  deriving DecidableEq

variable {N' : Type*} [DecidableEq N'] [hfn : HasFeatureNames N F N']

def embedPkg (F : Type*) [hfn : HasFeatureNames N F N'] (p : Package N V) : Package N' V :=
  (hfn.origN p.1, p.2)

def embedSet (F : Type*) [DecidableEq N'] [hfn : HasFeatureNames N F N'] (S : Finset (Package N V)) : Finset (Package N' V) :=
  S.image (embedPkg F)

def featureReal (R_f : Real N V) (support : Support N V F) :
    Real N' V :=
  embedSet F R_f ∪
  (support.biUnion (fun ⟨⟨n, v⟩, f⟩ =>
    if (n, v) ∈ R_f then {(hfn.featuredN n f, v)} else ∅))

def featureDeps (R_f : Real N V) (support : Support N V F)
    (Δ_f : FeatDepRel N V F) (Δ_a : AddlDepRel N V F) :
    DepRel N' V :=
  -- Feature packages depend on their base: (⟨n, f⟩, v) Δ (n, {v})
  (support.biUnion (fun ⟨⟨n, v⟩, f⟩ =>
    if (n, v) ∈ R_f then {((hfn.featuredN n f, v), hfn.origN n, {v})} else ∅)) ∪
  -- Parameterised deps with no features: p Δ (n, vs)
  ((Δ_f.filter (fun ⟨_, _, _, fs⟩ => fs = ∅)).image
    (fun ⟨p, n, vs, _⟩ => (embedPkg F p, hfn.origN n, vs))) ∪
  -- Parameterised deps with features: ∀ f ∈ fs, p Δ (⟨n, f⟩, vs)
  ((Δ_f.filter (fun ⟨_, _, _, fs⟩ => fs.Nonempty)).biUnion
    (fun ⟨p, n, vs, fs⟩ => fs.image (fun f => (embedPkg F p, hfn.featuredN n f, vs)))) ∪
  -- Additional deps with no features: (⟨n, f⟩, v) Δ (m, vs)
  ((Δ_a.filter (fun ⟨_, _, _, fs⟩ => fs = ∅)).image
    (fun ⟨⟨⟨n, v⟩, f⟩, m, vs, _⟩ => ((hfn.featuredN n f, v), hfn.origN m, vs))) ∪
  -- Additional deps with features: (⟨n, f⟩, v) Δ (⟨m, f'⟩, vs)
  ((Δ_a.filter (fun ⟨_, _, _, fs⟩ => fs.Nonempty)).biUnion
    (fun ⟨⟨⟨n, v⟩, f⟩, m, vs, fs⟩ =>
      fs.image (fun f' => ((hfn.featuredN n f, v), hfn.featuredN m f', vs))))

end PackageCalculus.Feature

namespace PackageCalculus

open Function

variable {N F : Type*}

instance : Feature.HasFeatureNames N F (Feature.FeatureName N F) where
  origN := ⟨Feature.FeatureName.orig, fun _ _ h => Feature.FeatureName.orig.inj h⟩
  featuredN := Feature.FeatureName.featured
  featuredN_injective := by
    intro a₁ a₂ b₁ b₂ h
    exact ⟨Feature.FeatureName.featured.inj h |>.1,
           Feature.FeatureName.featured.inj h |>.2⟩
  origN_ne_featuredN := fun _ _ _ => nofun
  featuredN_ne_origN := fun _ _ _ => nofun
  tryOrigN := fun
    | .orig n => some n
    | _ => none
  tryOrigN_origN := fun _ => rfl
  tryOrigN_some := fun n' n h => by
    cases n' with
    | orig m => simp at h; subst h; rfl
    | featured _ _ => simp at h
  tryFeaturedN := fun
    | .featured n f => some (n, f)
    | _ => none
  tryFeaturedN_featuredN := fun _ _ => rfl
  tryFeaturedN_some := fun n' p h => by
    cases n' with
    | featured n f => simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
    | orig _ => simp at h

end PackageCalculus
