import PackageCalculus.Composition.FeatureConcurrent.Types
import PackageCalculus.Composition.FeatureConcurrent.Definition
import PackageCalculus.Extensions.Feature.Reduction.Definition
import PackageCalculus.Extensions.Concurrent.Reduction.Definition
import Mathlib

/-! # Feature-concurrent composition: reduction

`concurrentFeatureReal` and `concurrentFeatureDeps` encode the combined feature
and concurrent problem into a core resolution problem. The encoding emits a
shared intermediate plus per-feature secondaries linked by back-edges that
enforce version alignment. -/

namespace PackageCalculus.Composition

open Classical

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {F : Type*} [DecidableEq F] {G : Type*} [DecidableEq G]
variable {N_FC : Type*} [DecidableEq N_FC] {V_FC : Type*} [DecidableEq V_FC]
variable [hcnm : Concurrent.HasConcurrentNames (Feature.FeatureName N F) V G N_FC]
variable [hcvr : Concurrent.HasConcurrentVersions V G V_FC]
variable [hcfi : HasConcurrentFeatureIntermediate N V F G N_FC]

set_option linter.unusedSectionVars false

/-- Resolve membership in a left-nested `Finset` union by backtracking search:
`mem_unions t` closes `x ∈ s₁ ∪ ⋯ ∪ sₙ` given a proof `t` of membership in one
of the components. -/
syntax "mem_unions " term : tactic
macro_rules
  | `(tactic| mem_unions $t) =>
    `(tactic| first
        | exact $t
        | (apply Finset.mem_union_left; mem_unions $t)
        | (apply Finset.mem_union_right; mem_unions $t))

/-! ### Joint feature-concurrent reduction

For each base depender-dependee pair `((n, v), m)` arising in any `Δ_f` or
`Δ_a` entry, a single shared intermediate `cfIntermediate n v m` is
introduced. The intermediate carries the full version `u` (peer-style) rather
than the granularity bucket `g(u)`, so that version uniqueness on the
intermediate pins `u` to a single element of the intersection of the sharing
entries' version sets.

For each contributing entry with version set `vs` and feature set `fs`:
* `(i, origV u) ∈ R` for each `u ∈ vs`;
* `(granular ⟨n, v⟩, origV v) Δ (i, vs.map origV)` (depender → intermediate);
* `(i, origV u) Δ (granular ⟨m, g u⟩, {origV u})` (intermediate → orig dependee) for each `u ∈ vs`;
* `(i, origV u) Δ (granular ⟨⟨m, f⟩, g u⟩, {origV u})` (intermediate → feature dependee)
  for each `(u, f) ∈ vs × fs`.

The bare Concurrent reduction's `intermediateN` packages are not used by this
encoding. -/

def concurrentFeatureReal
    (R : Real N V) (support : Feature.Support N V F)
    (Δ_f : Feature.FeatDepRel N V F) (Δ_a : Feature.AddlDepRel N V F)
    (g : V → G) : Real N_FC V_FC :=
  -- Granular packages: image of the feature-level real under the concurrent embedding.
  Concurrent.embedReal (Feature.featureReal R support) g ∪
  -- Shared concurrent-feature intermediates from Δ_f: `(cfIntermediate n v m, origV u)`
  -- for each `u ∈ vs`.
  (Δ_f.biUnion (fun ⟨⟨n, v⟩, m, vs, _⟩ =>
    vs.image (fun u => (hcfi.cfIntermediateN n v m, hcvr.origV u)))) ∪
  -- Per-feature secondary intermediates from Δ_f: `(cfIntermediateN_f n v m f, origV u)`
  -- for each `(u, f) ∈ vs × fs`.
  (Δ_f.biUnion (fun ⟨⟨n, v⟩, m, vs, fs⟩ =>
    vs.biUnion (fun u =>
      fs.image (fun f => (hcfi.cfIntermediateN_f n v m f, hcvr.origV u))))) ∪
  -- Shared concurrent-feature intermediates from Δ_a: same shape; the feature annotation `f`
  -- on the depender is irrelevant -- the shared intermediate keys only on `((n, v), m)`.
  (Δ_a.biUnion (fun ⟨⟨⟨n, v⟩, _⟩, m, vs, _⟩ =>
    vs.image (fun u => (hcfi.cfIntermediateN n v m, hcvr.origV u)))) ∪
  -- Per-feature secondary intermediates from Δ_a:
  -- `(cfIntermediateN_a n v f m f', origV u)` for each `(u, f') ∈ vs × fs`.
  (Δ_a.biUnion (fun ⟨⟨⟨n, v⟩, f⟩, m, vs, fs⟩ =>
    vs.biUnion (fun u =>
      fs.image (fun f' => (hcfi.cfIntermediateN_a n v f m f', hcvr.origV u)))))

def concurrentFeatureDeps
    (R : Real N V) (support : Feature.Support N V F)
    (Δ_f : Feature.FeatDepRel N V F) (Δ_a : Feature.AddlDepRel N V F)
    (g : V → G) : DepRel N_FC V_FC :=
  -- Feature back-deps from support:
  -- `(granularN (featured n f) (g v), origV v) Δ (granularN (orig n) (g v), {origV v})`.
  (support.biUnion (fun ⟨⟨n, v⟩, f⟩ =>
    if (n, v) ∈ R then
      {((hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v),
        hcnm.granularN (Feature.FeatureName.orig n) (g v),
        (({v} : Finset V).map hcvr.origV))}
    else ∅)) ∪
  -- Δ_f: depender → shared intermediate, one edge per `((n, v), m, vs)` entry.
  (Δ_f.biUnion (fun ⟨⟨n, v⟩, m, vs, _⟩ =>
    {((hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v),
      hcfi.cfIntermediateN n v m,
      vs.map hcvr.origV)})) ∪
  -- Δ_f: shared intermediate → orig dependee, one per `u ∈ vs`.
  (Δ_f.biUnion (fun ⟨⟨n, v⟩, m, vs, _⟩ =>
    vs.image (fun u =>
      ((hcfi.cfIntermediateN n v m, hcvr.origV u),
       hcnm.granularN (Feature.FeatureName.orig m) (g u),
       (({u} : Finset V).map hcvr.origV))))) ∪
  -- Δ_f: depender → per-feature secondary intermediate, one per `f ∈ fs`.
  (Δ_f.biUnion (fun ⟨⟨n, v⟩, m, vs, fs⟩ =>
    fs.image (fun f =>
      ((hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v),
       hcfi.cfIntermediateN_f n v m f,
       vs.map hcvr.origV)))) ∪
  -- Δ_f: per-feature secondary intermediate → feature dependee, one per `(u, f) ∈ vs × fs`.
  (Δ_f.biUnion (fun ⟨⟨n, v⟩, m, vs, fs⟩ =>
    vs.biUnion (fun u =>
      fs.image (fun f =>
        ((hcfi.cfIntermediateN_f n v m f, hcvr.origV u),
         hcnm.granularN (Feature.FeatureName.featured m f) (g u),
         (({u} : Finset V).map hcvr.origV)))))) ∪
  -- Δ_f: per-feature secondary intermediate → shared intermediate (back-edge for
  -- version alignment), one per `(u, f) ∈ vs × fs`.
  (Δ_f.biUnion (fun ⟨⟨n, v⟩, m, vs, fs⟩ =>
    fs.biUnion (fun f =>
      vs.image (fun u =>
        ((hcfi.cfIntermediateN_f n v m f, hcvr.origV u),
         hcfi.cfIntermediateN n v m,
         (({u} : Finset V).map hcvr.origV)))))) ∪
  -- Δ_a: depender → shared intermediate.
  (Δ_a.biUnion (fun ⟨⟨⟨n, v⟩, f⟩, m, vs, _⟩ =>
    {((hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v),
      hcfi.cfIntermediateN n v m,
      vs.map hcvr.origV)})) ∪
  -- Δ_a: shared intermediate → orig dependee, one per `u ∈ vs`.
  (Δ_a.biUnion (fun ⟨⟨⟨n, v⟩, _⟩, m, vs, _⟩ =>
    vs.image (fun u =>
      ((hcfi.cfIntermediateN n v m, hcvr.origV u),
       hcnm.granularN (Feature.FeatureName.orig m) (g u),
       (({u} : Finset V).map hcvr.origV))))) ∪
  -- Δ_a: depender's featured package → per-feature secondary intermediate, one per `f' ∈ fs`.
  (Δ_a.biUnion (fun ⟨⟨⟨n, v⟩, f⟩, m, vs, fs⟩ =>
    fs.image (fun f' =>
      ((hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v),
       hcfi.cfIntermediateN_a n v f m f',
       vs.map hcvr.origV)))) ∪
  -- Δ_a: per-feature secondary intermediate → feature dependee.
  (Δ_a.biUnion (fun ⟨⟨⟨n, v⟩, f⟩, m, vs, fs⟩ =>
    vs.biUnion (fun u =>
      fs.image (fun f' =>
        ((hcfi.cfIntermediateN_a n v f m f', hcvr.origV u),
         hcnm.granularN (Feature.FeatureName.featured m f') (g u),
         (({u} : Finset V).map hcvr.origV)))))) ∪
  -- Δ_a: per-feature secondary intermediate → shared intermediate (back-edge for
  -- version alignment), one per `(u, f') ∈ vs × fs`.
  (Δ_a.biUnion (fun ⟨⟨⟨n, v⟩, f⟩, m, vs, fs⟩ =>
    fs.biUnion (fun f' =>
      vs.image (fun u =>
        ((hcfi.cfIntermediateN_a n v f m f', hcvr.origV u),
         hcfi.cfIntermediateN n v m,
         (({u} : Finset V).map hcvr.origV))))))

/-! ### Membership constructors for `concurrentFeatureDeps` -/

theorem mem_cfDeps_f_depToInter
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {n : N} {v : V} {m : N} {vs : Finset V} {fs : Finset F}
    (hdep : ((n, v), m, vs, fs) ∈ Δ_f) :
    ((hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v),
     hcfi.cfIntermediateN n v m,
     vs.map hcvr.origV) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨(n, v), m, vs, fs⟩, hdep, Finset.mem_singleton.mpr rfl⟩

theorem mem_cfDeps_f_interToOrig
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {n : N} {v : V} {m : N} {vs : Finset V} {fs : Finset F} {u : V}
    (hdep : ((n, v), m, vs, fs) ∈ Δ_f) (hv : u ∈ vs) :
    ((hcfi.cfIntermediateN n v m, hcvr.origV u),
     hcnm.granularN (Feature.FeatureName.orig m) (g u),
     (({u} : Finset V).map hcvr.origV)) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨(n, v), m, vs, fs⟩, hdep, Finset.mem_image.mpr ⟨u, hv, rfl⟩⟩

/-- Δ_f: depender's orig granular → per-feature secondary intermediate
    `cfIntermediateN_f n v m f` for each `f ∈ fs`. -/
theorem mem_cfDeps_f_depToInterFeat
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {n : N} {v : V} {m : N} {vs : Finset V} {fs : Finset F} {f : F}
    (hdep : ((n, v), m, vs, fs) ∈ Δ_f) (hf : f ∈ fs) :
    ((hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v),
     hcfi.cfIntermediateN_f n v m f,
     vs.map hcvr.origV) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨(n, v), m, vs, fs⟩, hdep, Finset.mem_image.mpr ⟨f, hf, rfl⟩⟩

/-- Δ_f: per-feature secondary intermediate `cfIntermediateN_f n v m f`
    at `origV u` → feature granular dependee `granularN (featured m f) (g u)`. -/
theorem mem_cfDeps_f_interToFeat
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {n : N} {v : V} {m : N} {vs : Finset V} {fs : Finset F} {u : V} {f : F}
    (hdep : ((n, v), m, vs, fs) ∈ Δ_f) (hv : u ∈ vs) (hf : f ∈ fs) :
    ((hcfi.cfIntermediateN_f n v m f, hcvr.origV u),
     hcnm.granularN (Feature.FeatureName.featured m f) (g u),
     (({u} : Finset V).map hcvr.origV)) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨(n, v), m, vs, fs⟩, hdep, Finset.mem_biUnion.mpr ⟨u, hv, Finset.mem_image.mpr ⟨f, hf, rfl⟩⟩⟩

/-- Δ_f: per-feature secondary intermediate `cfIntermediateN_f n v m f` at `origV u`
    → shared intermediate `cfIntermediateN n v m`. Back-edge enforcing version
    alignment between secondary and shared. -/
theorem mem_cfDeps_f_interFeatToInter
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {n : N} {v : V} {m : N} {vs : Finset V} {fs : Finset F} {u : V} {f : F}
    (hdep : ((n, v), m, vs, fs) ∈ Δ_f) (hu : u ∈ vs) (hf : f ∈ fs) :
    ((hcfi.cfIntermediateN_f n v m f, hcvr.origV u),
     hcfi.cfIntermediateN n v m,
     (({u} : Finset V).map hcvr.origV)) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨(n, v), m, vs, fs⟩, hdep, Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩⟩

theorem mem_cfDeps_a_depToInter
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {n : N} {v : V} {f : F} {m : N} {vs : Finset V} {fs : Finset F}
    (hdep : (((n, v), f), m, vs, fs) ∈ Δ_a) :
    ((hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v),
     hcfi.cfIntermediateN n v m,
     vs.map hcvr.origV) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨((n, v), f), m, vs, fs⟩, hdep, Finset.mem_singleton.mpr rfl⟩

theorem mem_cfDeps_a_interToOrig
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {n : N} {v : V} {f : F} {m : N} {vs : Finset V} {fs : Finset F} {u : V}
    (hdep : (((n, v), f), m, vs, fs) ∈ Δ_a) (hv : u ∈ vs) :
    ((hcfi.cfIntermediateN n v m, hcvr.origV u),
     hcnm.granularN (Feature.FeatureName.orig m) (g u),
     (({u} : Finset V).map hcvr.origV)) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨((n, v), f), m, vs, fs⟩, hdep, Finset.mem_image.mpr ⟨u, hv, rfl⟩⟩

/-- Δ_a: depender's featured granular `(featured n f, g v)` → per-feature secondary
    intermediate `cfIntermediateN_a n v f m f'` for each `f' ∈ fs`. -/
theorem mem_cfDeps_a_depToInterFeat
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {n : N} {v : V} {f : F} {m : N} {vs : Finset V} {fs : Finset F} {f' : F}
    (hdep : (((n, v), f), m, vs, fs) ∈ Δ_a) (hf' : f' ∈ fs) :
    ((hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v),
     hcfi.cfIntermediateN_a n v f m f',
     vs.map hcvr.origV) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨((n, v), f), m, vs, fs⟩, hdep, Finset.mem_image.mpr ⟨f', hf', rfl⟩⟩

/-- Δ_a: per-feature secondary intermediate `cfIntermediateN_a n v f m f'` at `origV u`
    → feature granular dependee `granularN (featured m f') (g u)`. -/
theorem mem_cfDeps_a_interToFeat
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {n : N} {v : V} {f : F} {m : N} {vs : Finset V} {fs : Finset F} {u : V} {f' : F}
    (hdep : (((n, v), f), m, vs, fs) ∈ Δ_a) (hv : u ∈ vs) (hf' : f' ∈ fs) :
    ((hcfi.cfIntermediateN_a n v f m f', hcvr.origV u),
     hcnm.granularN (Feature.FeatureName.featured m f') (g u),
     (({u} : Finset V).map hcvr.origV)) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨((n, v), f), m, vs, fs⟩, hdep, Finset.mem_biUnion.mpr ⟨u, hv, Finset.mem_image.mpr ⟨f', hf', rfl⟩⟩⟩

/-- Δ_a: per-feature secondary intermediate `cfIntermediateN_a n v f m f'` at `origV u`
    → shared intermediate `cfIntermediateN n v m`. Back-edge enforcing version
    alignment between secondary and shared. -/
theorem mem_cfDeps_a_interFeatToInter
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {n : N} {v : V} {f : F} {m : N} {vs : Finset V} {fs : Finset F} {u : V} {f' : F}
    (hdep : (((n, v), f), m, vs, fs) ∈ Δ_a) (hu : u ∈ vs) (hf' : f' ∈ fs) :
    ((hcfi.cfIntermediateN_a n v f m f', hcvr.origV u),
     hcfi.cfIntermediateN n v m,
     (({u} : Finset V).map hcvr.origV)) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨((n, v), f), m, vs, fs⟩, hdep, Finset.mem_biUnion.mpr ⟨f', hf', Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩⟩

/-! ### Membership constructors for `concurrentFeatureReal` -/

theorem mem_cfReal_inter_f
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {n : N} {v : V} {m : N} {vs : Finset V} {fs : Finset F} {u : V}
    (hdep : ((n, v), m, vs, fs) ∈ Δ_f) (hv : u ∈ vs) :
    (hcfi.cfIntermediateN n v m, hcvr.origV u) ∈
      concurrentFeatureReal R support Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨(n, v), m, vs, fs⟩, hdep, Finset.mem_image.mpr ⟨u, hv, rfl⟩⟩

/-- Per-feature secondary intermediate `cfIntermediateN_f n v m f` is in `R` for each
    `(u, f) ∈ vs × fs` of a Δ_f entry. -/
theorem mem_cfReal_inter_f_feat
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {n : N} {v : V} {m : N} {vs : Finset V} {fs : Finset F} {u : V} {f : F}
    (hdep : ((n, v), m, vs, fs) ∈ Δ_f) (hv : u ∈ vs) (hf : f ∈ fs) :
    (hcfi.cfIntermediateN_f n v m f, hcvr.origV u) ∈
      concurrentFeatureReal R support Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨(n, v), m, vs, fs⟩, hdep, Finset.mem_biUnion.mpr ⟨u, hv, Finset.mem_image.mpr ⟨f, hf, rfl⟩⟩⟩

theorem mem_cfReal_inter_a
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {n : N} {v : V} {f : F} {m : N} {vs : Finset V} {fs : Finset F} {u : V}
    (hdep : (((n, v), f), m, vs, fs) ∈ Δ_a) (hv : u ∈ vs) :
    (hcfi.cfIntermediateN n v m, hcvr.origV u) ∈
      concurrentFeatureReal R support Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨((n, v), f), m, vs, fs⟩, hdep, Finset.mem_image.mpr ⟨u, hv, rfl⟩⟩

/-- Per-feature secondary intermediate `cfIntermediateN_a n v f m f'` is in `R` for each
    `(u, f') ∈ vs × fs` of a Δ_a entry. -/
theorem mem_cfReal_inter_a_feat
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {n : N} {v : V} {f : F} {m : N} {vs : Finset V} {fs : Finset F} {u : V} {f' : F}
    (hdep : (((n, v), f), m, vs, fs) ∈ Δ_a) (hv : u ∈ vs) (hf' : f' ∈ fs) :
    (hcfi.cfIntermediateN_a n v f m f', hcvr.origV u) ∈
      concurrentFeatureReal R support Δ_f Δ_a g := by
  mem_unions Finset.mem_biUnion.mpr ⟨⟨((n, v), f), m, vs, fs⟩, hdep, Finset.mem_biUnion.mpr ⟨u, hv, Finset.mem_image.mpr ⟨f', hf', rfl⟩⟩⟩

/-! ### Reverse membership for `concurrentFeatureDeps` -/

theorem concurrentFeatureDeps_mem_cases
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F}
    {g : V → G}
    {p : Package N_FC V_FC} {m_fc : N_FC} {vs : Finset V_FC}
    (h : (p, m_fc, vs) ∈ concurrentFeatureDeps R support Δ_f Δ_a g) :
    -- supp_back
    (∃ n v f, (n, v) ∈ R ∧ ((n, v), f) ∈ support ∧
      p = (hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v) ∧
      m_fc = hcnm.granularN (Feature.FeatureName.orig n) (g v) ∧
      vs = ({v} : Finset V).map hcvr.origV) ∨
    -- f_depToInter
    (∃ n v m vs_raw fs, ((n, v), m, vs_raw, fs) ∈ Δ_f ∧
      p = (hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v) ∧
      m_fc = hcfi.cfIntermediateN n v m ∧
      vs = vs_raw.map hcvr.origV) ∨
    -- f_interToOrig
    (∃ n v m vs_raw fs u, ((n, v), m, vs_raw, fs) ∈ Δ_f ∧ u ∈ vs_raw ∧
      p = (hcfi.cfIntermediateN n v m, hcvr.origV u) ∧
      m_fc = hcnm.granularN (Feature.FeatureName.orig m) (g u) ∧
      vs = ({u} : Finset V).map hcvr.origV) ∨
    -- f_depToInterFeat
    (∃ n v m vs_raw fs f, ((n, v), m, vs_raw, fs) ∈ Δ_f ∧ f ∈ fs ∧
      p = (hcnm.granularN (Feature.FeatureName.orig n) (g v), hcvr.origV v) ∧
      m_fc = hcfi.cfIntermediateN_f n v m f ∧
      vs = vs_raw.map hcvr.origV) ∨
    -- f_interToFeat
    (∃ n v m vs_raw fs u f, ((n, v), m, vs_raw, fs) ∈ Δ_f ∧ u ∈ vs_raw ∧ f ∈ fs ∧
      p = (hcfi.cfIntermediateN_f n v m f, hcvr.origV u) ∧
      m_fc = hcnm.granularN (Feature.FeatureName.featured m f) (g u) ∧
      vs = ({u} : Finset V).map hcvr.origV) ∨
    -- f_interFeatToInter (back-edge)
    (∃ n v m vs_raw fs u f, ((n, v), m, vs_raw, fs) ∈ Δ_f ∧ u ∈ vs_raw ∧ f ∈ fs ∧
      p = (hcfi.cfIntermediateN_f n v m f, hcvr.origV u) ∧
      m_fc = hcfi.cfIntermediateN n v m ∧
      vs = ({u} : Finset V).map hcvr.origV) ∨
    -- a_depToInter
    (∃ n v f m vs_raw fs, (((n, v), f), m, vs_raw, fs) ∈ Δ_a ∧
      p = (hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v) ∧
      m_fc = hcfi.cfIntermediateN n v m ∧
      vs = vs_raw.map hcvr.origV) ∨
    -- a_interToOrig
    (∃ n v f_dep m vs_raw fs u, (((n, v), f_dep), m, vs_raw, fs) ∈ Δ_a ∧ u ∈ vs_raw ∧
      p = (hcfi.cfIntermediateN n v m, hcvr.origV u) ∧
      m_fc = hcnm.granularN (Feature.FeatureName.orig m) (g u) ∧
      vs = ({u} : Finset V).map hcvr.origV) ∨
    -- a_depToInterFeat
    (∃ n v f_dep m vs_raw fs f', (((n, v), f_dep), m, vs_raw, fs) ∈ Δ_a ∧ f' ∈ fs ∧
      p = (hcnm.granularN (Feature.FeatureName.featured n f_dep) (g v), hcvr.origV v) ∧
      m_fc = hcfi.cfIntermediateN_a n v f_dep m f' ∧
      vs = vs_raw.map hcvr.origV) ∨
    -- a_interToFeat
    (∃ n v f_dep m vs_raw fs u f', (((n, v), f_dep), m, vs_raw, fs) ∈ Δ_a ∧
      u ∈ vs_raw ∧ f' ∈ fs ∧
      p = (hcfi.cfIntermediateN_a n v f_dep m f', hcvr.origV u) ∧
      m_fc = hcnm.granularN (Feature.FeatureName.featured m f') (g u) ∧
      vs = ({u} : Finset V).map hcvr.origV) ∨
    -- a_interFeatToInter (back-edge)
    (∃ n v f_dep m vs_raw fs u f', (((n, v), f_dep), m, vs_raw, fs) ∈ Δ_a ∧
      u ∈ vs_raw ∧ f' ∈ fs ∧
      p = (hcfi.cfIntermediateN_a n v f_dep m f', hcvr.origV u) ∧
      m_fc = hcfi.cfIntermediateN n v m ∧
      vs = ({u} : Finset V).map hcvr.origV) := by
  simp only [concurrentFeatureDeps, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_singleton] at h
  rcases h with (((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h
  · -- supp_back
    left
    obtain ⟨⟨⟨n, v⟩, f⟩, hsupp, hmem⟩ := h
    simp only at hmem
    split_ifs at hmem with hR
    · simp only [Finset.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      exact ⟨n, v, f, hR, hsupp, rfl, rfl, rfl⟩
    · exact absurd hmem (Finset.notMem_empty _)
  · -- f_depToInter
    right; left
    obtain ⟨⟨⟨n, v⟩, m, vs_raw, fs⟩, hdep, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨n, v, m, vs_raw, fs, hdep, rfl, rfl, rfl⟩
  · -- f_interToOrig
    right; right; left
    obtain ⟨⟨⟨n, v⟩, m, vs_raw, fs⟩, hdep, u, hv, heq⟩ := h
    simp only at hv
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨n, v, m, vs_raw, fs, u, hdep, hv, rfl, rfl, rfl⟩
  · -- f_depToInterFeat
    right; right; right; left
    obtain ⟨⟨⟨n, v⟩, m, vs_raw, fs⟩, hdep, f, hf, heq⟩ := h
    simp only at hf
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨n, v, m, vs_raw, fs, f, hdep, hf, rfl, rfl, rfl⟩
  · -- f_interToFeat
    right; right; right; right; left
    obtain ⟨⟨⟨n, v⟩, m, vs_raw, fs⟩, hdep, u, hv, f, hf, heq⟩ := h
    simp only at hv hf
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨n, v, m, vs_raw, fs, u, f, hdep, hv, hf, rfl, rfl, rfl⟩
  · -- f_interFeatToInter
    right; right; right; right; right; left
    obtain ⟨⟨⟨n, v⟩, m, vs_raw, fs⟩, hdep, f, hf, u, hu, heq⟩ := h
    simp only at hf hu
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨n, v, m, vs_raw, fs, u, f, hdep, hu, hf, rfl, rfl, rfl⟩
  · -- a_depToInter
    right; right; right; right; right; right; left
    obtain ⟨⟨⟨⟨n, v⟩, f⟩, m, vs_raw, fs⟩, hdep, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨n, v, f, m, vs_raw, fs, hdep, rfl, rfl, rfl⟩
  · -- a_interToOrig
    right; right; right; right; right; right; right; left
    obtain ⟨⟨⟨⟨n, v⟩, f⟩, m, vs_raw, fs⟩, hdep, u, hv, heq⟩ := h
    simp only at hv
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨n, v, f, m, vs_raw, fs, u, hdep, hv, rfl, rfl, rfl⟩
  · -- a_depToInterFeat
    right; right; right; right; right; right; right; right; left
    obtain ⟨⟨⟨⟨n, v⟩, f⟩, m, vs_raw, fs⟩, hdep, f', hf', heq⟩ := h
    simp only at hf'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨n, v, f, m, vs_raw, fs, f', hdep, hf', rfl, rfl, rfl⟩
  · -- a_interToFeat
    right; right; right; right; right; right; right; right; right; left
    obtain ⟨⟨⟨⟨n, v⟩, f⟩, m, vs_raw, fs⟩, hdep, u, hv, f', hf', heq⟩ := h
    simp only at hv hf'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨n, v, f, m, vs_raw, fs, u, f', hdep, hv, hf', rfl, rfl, rfl⟩
  · -- a_interFeatToInter
    right; right; right; right; right; right; right; right; right; right
    obtain ⟨⟨⟨⟨n, v⟩, f⟩, m, vs_raw, fs⟩, hdep, f', hf', u, hu, heq⟩ := h
    simp only at hf' hu
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨n, v, f, m, vs_raw, fs, u, f', hdep, hu, hf', rfl, rfl, rfl⟩

end PackageCalculus.Composition
