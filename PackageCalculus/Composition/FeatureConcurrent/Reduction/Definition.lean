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

/-! ### Joint feature-concurrent reduction

For each base depender-dependee pair `((p_n, p_v), n)` arising in any `Δ_f` or
`Δ_a` entry, a single shared intermediate `cfIntermediate p_n p_v n` is
introduced. The intermediate carries the full version `v` (peer-style) rather
than the granularity bucket `g(v)`, so that version uniqueness on the
intermediate pins `v` to a single element of the intersection of the sharing
entries' version sets.

For each contributing entry with version set `vs` and feature set `fs`:
* `(i, origV v) ∈ R` for each `v ∈ vs`;
* `(granular ⟨p, p_v⟩, origV p_v) Δ (i, vs.map origV)` (depender → intermediate);
* `(i, origV v) Δ (granular ⟨n, g v⟩, {origV v})` (intermediate → orig dependee) for each `v ∈ vs`;
* `(i, origV v) Δ (granular ⟨⟨n, f⟩, g v⟩, {origV v})` (intermediate → feature dependee)
  for each `(v, f) ∈ vs × fs`.

The bare Concurrent reduction's `intermediateN` packages are not used by this
encoding. -/

def concurrentFeatureReal
    (R : Real N V) (support : Feature.Support N V F)
    (Δ_f : Feature.FeatDepRel N V F) (Δ_a : Feature.AddlDepRel N V F)
    (g : V → G) : Real N_FC V_FC :=
  -- Granular packages: image of the feature-level real under the concurrent embedding.
  Concurrent.embedReal (Feature.featureReal R support) g ∪
  -- Shared concurrent-feature intermediates from Δ_f: `(cfIntermediate p_n p_v n, origV v)`
  -- for each `v ∈ vs`.
  (Δ_f.biUnion (fun ⟨⟨p_n, p_v⟩, n, vs, _⟩ =>
    vs.image (fun v => (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v)))) ∪
  -- Per-feature secondary intermediates from Δ_f: `(cfIntermediateN_f p_n p_v n f, origV v)`
  -- for each `(v, f) ∈ vs × fs`.
  (Δ_f.biUnion (fun ⟨⟨p_n, p_v⟩, n, vs, fs⟩ =>
    vs.biUnion (fun v =>
      fs.image (fun f => (hcfi.cfIntermediateN_f p_n p_v n f, hcvr.origV v))))) ∪
  -- Shared concurrent-feature intermediates from Δ_a: same shape; the feature annotation `f`
  -- on the depender is irrelevant -- the shared intermediate keys only on `((p_n, p_v), n)`.
  (Δ_a.biUnion (fun ⟨⟨⟨p_n, p_v⟩, _⟩, n, vs, _⟩ =>
    vs.image (fun v => (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v)))) ∪
  -- Per-feature secondary intermediates from Δ_a:
  -- `(cfIntermediateN_a p_n p_v f n f', origV v)` for each `(v, f') ∈ vs × fs`.
  (Δ_a.biUnion (fun ⟨⟨⟨p_n, p_v⟩, f⟩, n, vs, fs⟩ =>
    vs.biUnion (fun v =>
      fs.image (fun f' => (hcfi.cfIntermediateN_a p_n p_v f n f', hcvr.origV v)))))

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
  -- Δ_f: depender → shared intermediate, one edge per `((p_n, p_v), n, vs)` entry.
  (Δ_f.biUnion (fun ⟨⟨p_n, p_v⟩, n, vs, _⟩ =>
    {((hcnm.granularN (Feature.FeatureName.orig p_n) (g p_v), hcvr.origV p_v),
      hcfi.cfIntermediateN p_n p_v n,
      vs.map hcvr.origV)})) ∪
  -- Δ_f: shared intermediate → orig dependee, one per `v ∈ vs`.
  (Δ_f.biUnion (fun ⟨⟨p_n, p_v⟩, n, vs, _⟩ =>
    vs.image (fun v =>
      ((hcfi.cfIntermediateN p_n p_v n, hcvr.origV v),
       hcnm.granularN (Feature.FeatureName.orig n) (g v),
       (({v} : Finset V).map hcvr.origV))))) ∪
  -- Δ_f: depender → per-feature secondary intermediate, one per `f ∈ fs`.
  (Δ_f.biUnion (fun ⟨⟨p_n, p_v⟩, n, vs, fs⟩ =>
    fs.image (fun f =>
      ((hcnm.granularN (Feature.FeatureName.orig p_n) (g p_v), hcvr.origV p_v),
       hcfi.cfIntermediateN_f p_n p_v n f,
       vs.map hcvr.origV)))) ∪
  -- Δ_f: per-feature secondary intermediate → feature dependee, one per `(v, f) ∈ vs × fs`.
  (Δ_f.biUnion (fun ⟨⟨p_n, p_v⟩, n, vs, fs⟩ =>
    vs.biUnion (fun v =>
      fs.image (fun f =>
        ((hcfi.cfIntermediateN_f p_n p_v n f, hcvr.origV v),
         hcnm.granularN (Feature.FeatureName.featured n f) (g v),
         (({v} : Finset V).map hcvr.origV)))))) ∪
  -- Δ_f: per-feature secondary intermediate → shared intermediate (back-edge for
  -- version alignment), one per `(v, f) ∈ vs × fs`.
  (Δ_f.biUnion (fun ⟨⟨p_n, p_v⟩, n, vs, fs⟩ =>
    fs.biUnion (fun f =>
      vs.image (fun u =>
        ((hcfi.cfIntermediateN_f p_n p_v n f, hcvr.origV u),
         hcfi.cfIntermediateN p_n p_v n,
         (({u} : Finset V).map hcvr.origV)))))) ∪
  -- Δ_a: depender → shared intermediate.
  (Δ_a.biUnion (fun ⟨⟨⟨p_n, p_v⟩, f⟩, n, vs, _⟩ =>
    {((hcnm.granularN (Feature.FeatureName.featured p_n f) (g p_v), hcvr.origV p_v),
      hcfi.cfIntermediateN p_n p_v n,
      vs.map hcvr.origV)})) ∪
  -- Δ_a: shared intermediate → orig dependee, one per `v ∈ vs`.
  (Δ_a.biUnion (fun ⟨⟨⟨p_n, p_v⟩, _⟩, n, vs, _⟩ =>
    vs.image (fun v =>
      ((hcfi.cfIntermediateN p_n p_v n, hcvr.origV v),
       hcnm.granularN (Feature.FeatureName.orig n) (g v),
       (({v} : Finset V).map hcvr.origV))))) ∪
  -- Δ_a: depender's featured package → per-feature secondary intermediate, one per `f' ∈ fs`.
  (Δ_a.biUnion (fun ⟨⟨⟨p_n, p_v⟩, f⟩, n, vs, fs⟩ =>
    fs.image (fun f' =>
      ((hcnm.granularN (Feature.FeatureName.featured p_n f) (g p_v), hcvr.origV p_v),
       hcfi.cfIntermediateN_a p_n p_v f n f',
       vs.map hcvr.origV)))) ∪
  -- Δ_a: per-feature secondary intermediate → feature dependee.
  (Δ_a.biUnion (fun ⟨⟨⟨p_n, p_v⟩, f⟩, n, vs, fs⟩ =>
    vs.biUnion (fun v =>
      fs.image (fun f' =>
        ((hcfi.cfIntermediateN_a p_n p_v f n f', hcvr.origV v),
         hcnm.granularN (Feature.FeatureName.featured n f') (g v),
         (({v} : Finset V).map hcvr.origV)))))) ∪
  -- Δ_a: per-feature secondary intermediate → shared intermediate (back-edge for
  -- version alignment), one per `(v, f') ∈ vs × fs`.
  (Δ_a.biUnion (fun ⟨⟨⟨p_n, p_v⟩, f⟩, n, vs, fs⟩ =>
    fs.biUnion (fun f' =>
      vs.image (fun u =>
        ((hcfi.cfIntermediateN_a p_n p_v f n f', hcvr.origV u),
         hcfi.cfIntermediateN p_n p_v n,
         (({u} : Finset V).map hcvr.origV))))))

/-! ### Membership constructors for `concurrentFeatureDeps` -/

theorem mem_cfDeps_f_depToInter
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {p_n : N} {p_v : V} {n : N} {vs : Finset V} {fs : Finset F}
    (hdep : ((p_n, p_v), n, vs, fs) ∈ Δ_f) :
    ((hcnm.granularN (Feature.FeatureName.orig p_n) (g p_v), hcvr.origV p_v),
     hcfi.cfIntermediateN p_n p_v n,
     vs.map hcvr.origV) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨(p_n, p_v), n, vs, fs⟩, hdep, ?_⟩
  exact Finset.mem_singleton.mpr rfl

theorem mem_cfDeps_f_interToOrig
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {p_n : N} {p_v : V} {n : N} {vs : Finset V} {fs : Finset F} {v : V}
    (hdep : ((p_n, p_v), n, vs, fs) ∈ Δ_f) (hv : v ∈ vs) :
    ((hcfi.cfIntermediateN p_n p_v n, hcvr.origV v),
     hcnm.granularN (Feature.FeatureName.orig n) (g v),
     (({v} : Finset V).map hcvr.origV)) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨(p_n, p_v), n, vs, fs⟩, hdep, ?_⟩
  exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- Δ_f: depender's orig granular → per-feature secondary intermediate
    `cfIntermediateN_f p_n p_v n f` for each `f ∈ fs`. -/
theorem mem_cfDeps_f_depToInterFeat
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {p_n : N} {p_v : V} {n : N} {vs : Finset V} {fs : Finset F} {f : F}
    (hdep : ((p_n, p_v), n, vs, fs) ∈ Δ_f) (hf : f ∈ fs) :
    ((hcnm.granularN (Feature.FeatureName.orig p_n) (g p_v), hcvr.origV p_v),
     hcfi.cfIntermediateN_f p_n p_v n f,
     vs.map hcvr.origV) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨(p_n, p_v), n, vs, fs⟩, hdep, ?_⟩
  exact Finset.mem_image.mpr ⟨f, hf, rfl⟩

/-- Δ_f: per-feature secondary intermediate `cfIntermediateN_f p_n p_v n f`
    at `origV v` → feature granular dependee `granularN (featured n f) (g v)`. -/
theorem mem_cfDeps_f_interToFeat
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {p_n : N} {p_v : V} {n : N} {vs : Finset V} {fs : Finset F} {v : V} {f : F}
    (hdep : ((p_n, p_v), n, vs, fs) ∈ Δ_f) (hv : v ∈ vs) (hf : f ∈ fs) :
    ((hcfi.cfIntermediateN_f p_n p_v n f, hcvr.origV v),
     hcnm.granularN (Feature.FeatureName.featured n f) (g v),
     (({v} : Finset V).map hcvr.origV)) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨(p_n, p_v), n, vs, fs⟩, hdep, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨f, hf, rfl⟩⟩

/-- Δ_f: per-feature secondary intermediate `cfIntermediateN_f p_n p_v n f` at `origV u`
    → shared intermediate `cfIntermediateN p_n p_v n`. Back-edge enforcing version
    alignment between secondary and shared. -/
theorem mem_cfDeps_f_interFeatToInter
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {p_n : N} {p_v : V} {n : N} {vs : Finset V} {fs : Finset F} {u : V} {f : F}
    (hdep : ((p_n, p_v), n, vs, fs) ∈ Δ_f) (hu : u ∈ vs) (hf : f ∈ fs) :
    ((hcfi.cfIntermediateN_f p_n p_v n f, hcvr.origV u),
     hcfi.cfIntermediateN p_n p_v n,
     (({u} : Finset V).map hcvr.origV)) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨(p_n, p_v), n, vs, fs⟩, hdep, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩

theorem mem_cfDeps_a_depToInter
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {p_n : N} {p_v : V} {f : F} {n : N} {vs : Finset V} {fs : Finset F}
    (hdep : (((p_n, p_v), f), n, vs, fs) ∈ Δ_a) :
    ((hcnm.granularN (Feature.FeatureName.featured p_n f) (g p_v), hcvr.origV p_v),
     hcfi.cfIntermediateN p_n p_v n,
     vs.map hcvr.origV) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨((p_n, p_v), f), n, vs, fs⟩, hdep, ?_⟩
  exact Finset.mem_singleton.mpr rfl

theorem mem_cfDeps_a_interToOrig
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {p_n : N} {p_v : V} {f : F} {n : N} {vs : Finset V} {fs : Finset F} {v : V}
    (hdep : (((p_n, p_v), f), n, vs, fs) ∈ Δ_a) (hv : v ∈ vs) :
    ((hcfi.cfIntermediateN p_n p_v n, hcvr.origV v),
     hcnm.granularN (Feature.FeatureName.orig n) (g v),
     (({v} : Finset V).map hcvr.origV)) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨((p_n, p_v), f), n, vs, fs⟩, hdep, ?_⟩
  exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- Δ_a: depender's featured granular `(featured p_n f, g p_v)` → per-feature secondary
    intermediate `cfIntermediateN_a p_n p_v f n f'` for each `f' ∈ fs`. -/
theorem mem_cfDeps_a_depToInterFeat
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {p_n : N} {p_v : V} {f : F} {n : N} {vs : Finset V} {fs : Finset F} {f' : F}
    (hdep : (((p_n, p_v), f), n, vs, fs) ∈ Δ_a) (hf' : f' ∈ fs) :
    ((hcnm.granularN (Feature.FeatureName.featured p_n f) (g p_v), hcvr.origV p_v),
     hcfi.cfIntermediateN_a p_n p_v f n f',
     vs.map hcvr.origV) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨((p_n, p_v), f), n, vs, fs⟩, hdep, ?_⟩
  exact Finset.mem_image.mpr ⟨f', hf', rfl⟩

/-- Δ_a: per-feature secondary intermediate `cfIntermediateN_a p_n p_v f n f'` at `origV v`
    → feature granular dependee `granularN (featured n f') (g v)`. -/
theorem mem_cfDeps_a_interToFeat
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {p_n : N} {p_v : V} {f : F} {n : N} {vs : Finset V} {fs : Finset F} {v : V} {f' : F}
    (hdep : (((p_n, p_v), f), n, vs, fs) ∈ Δ_a) (hv : v ∈ vs) (hf' : f' ∈ fs) :
    ((hcfi.cfIntermediateN_a p_n p_v f n f', hcvr.origV v),
     hcnm.granularN (Feature.FeatureName.featured n f') (g v),
     (({v} : Finset V).map hcvr.origV)) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨((p_n, p_v), f), n, vs, fs⟩, hdep, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨f', hf', rfl⟩⟩

/-- Δ_a: per-feature secondary intermediate `cfIntermediateN_a p_n p_v f n f'` at `origV u`
    → shared intermediate `cfIntermediateN p_n p_v n`. Back-edge enforcing version
    alignment between secondary and shared. -/
theorem mem_cfDeps_a_interFeatToInter
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {p_n : N} {p_v : V} {f : F} {n : N} {vs : Finset V} {fs : Finset F} {u : V} {f' : F}
    (hdep : (((p_n, p_v), f), n, vs, fs) ∈ Δ_a) (hu : u ∈ vs) (hf' : f' ∈ fs) :
    ((hcfi.cfIntermediateN_a p_n p_v f n f', hcvr.origV u),
     hcfi.cfIntermediateN p_n p_v n,
     (({u} : Finset V).map hcvr.origV)) ∈ concurrentFeatureDeps R support Δ_f Δ_a g := by
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨((p_n, p_v), f), n, vs, fs⟩, hdep, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨f', hf', Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩

/-! ### Membership constructors for `concurrentFeatureReal` -/

theorem mem_cfReal_inter_f
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {p_n : N} {p_v : V} {n : N} {vs : Finset V} {fs : Finset F} {v : V}
    (hdep : ((p_n, p_v), n, vs, fs) ∈ Δ_f) (hv : v ∈ vs) :
    (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v) ∈
      concurrentFeatureReal R support Δ_f Δ_a g := by
  apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨(p_n, p_v), n, vs, fs⟩, hdep, ?_⟩
  exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- Per-feature secondary intermediate `cfIntermediateN_f p_n p_v n f` is in `R` for each
    `(v, f) ∈ vs × fs` of a Δ_f entry. -/
theorem mem_cfReal_inter_f_feat
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {p_n : N} {p_v : V} {n : N} {vs : Finset V} {fs : Finset F} {v : V} {f : F}
    (hdep : ((p_n, p_v), n, vs, fs) ∈ Δ_f) (hv : v ∈ vs) (hf : f ∈ fs) :
    (hcfi.cfIntermediateN_f p_n p_v n f, hcvr.origV v) ∈
      concurrentFeatureReal R support Δ_f Δ_a g := by
  apply Finset.mem_union_left; apply Finset.mem_union_left
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨(p_n, p_v), n, vs, fs⟩, hdep, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨f, hf, rfl⟩⟩

theorem mem_cfReal_inter_a
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {p_n : N} {p_v : V} {f : F} {n : N} {vs : Finset V} {fs : Finset F} {v : V}
    (hdep : (((p_n, p_v), f), n, vs, fs) ∈ Δ_a) (hv : v ∈ vs) :
    (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v) ∈
      concurrentFeatureReal R support Δ_f Δ_a g := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨((p_n, p_v), f), n, vs, fs⟩, hdep, ?_⟩
  exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- Per-feature secondary intermediate `cfIntermediateN_a p_n p_v f n f'` is in `R` for each
    `(v, f') ∈ vs × fs` of a Δ_a entry. -/
theorem mem_cfReal_inter_a_feat
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F} {g : V → G}
    {p_n : N} {p_v : V} {f : F} {n : N} {vs : Finset V} {fs : Finset F} {v : V} {f' : F}
    (hdep : (((p_n, p_v), f), n, vs, fs) ∈ Δ_a) (hv : v ∈ vs) (hf' : f' ∈ fs) :
    (hcfi.cfIntermediateN_a p_n p_v f n f', hcvr.origV v) ∈
      concurrentFeatureReal R support Δ_f Δ_a g := by
  apply Finset.mem_union_right
  refine Finset.mem_biUnion.mpr ⟨⟨((p_n, p_v), f), n, vs, fs⟩, hdep, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨f', hf', rfl⟩⟩

/-! ### Reverse membership for `concurrentFeatureDeps` -/

theorem concurrentFeatureDeps_mem_cases
    {R : Real N V} {support : Feature.Support N V F}
    {Δ_f : Feature.FeatDepRel N V F} {Δ_a : Feature.AddlDepRel N V F}
    {g : V → G}
    {p : Package N_FC V_FC} {m : N_FC} {vs : Finset V_FC}
    (h : (p, m, vs) ∈ concurrentFeatureDeps R support Δ_f Δ_a g) :
    -- supp_back
    (∃ n v f, (n, v) ∈ R ∧ ((n, v), f) ∈ support ∧
      p = (hcnm.granularN (Feature.FeatureName.featured n f) (g v), hcvr.origV v) ∧
      m = hcnm.granularN (Feature.FeatureName.orig n) (g v) ∧
      vs = ({v} : Finset V).map hcvr.origV) ∨
    -- f_depToInter
    (∃ p_n p_v n vs_raw fs, ((p_n, p_v), n, vs_raw, fs) ∈ Δ_f ∧
      p = (hcnm.granularN (Feature.FeatureName.orig p_n) (g p_v), hcvr.origV p_v) ∧
      m = hcfi.cfIntermediateN p_n p_v n ∧
      vs = vs_raw.map hcvr.origV) ∨
    -- f_interToOrig
    (∃ p_n p_v n vs_raw fs v, ((p_n, p_v), n, vs_raw, fs) ∈ Δ_f ∧ v ∈ vs_raw ∧
      p = (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v) ∧
      m = hcnm.granularN (Feature.FeatureName.orig n) (g v) ∧
      vs = ({v} : Finset V).map hcvr.origV) ∨
    -- f_depToInterFeat
    (∃ p_n p_v n vs_raw fs f, ((p_n, p_v), n, vs_raw, fs) ∈ Δ_f ∧ f ∈ fs ∧
      p = (hcnm.granularN (Feature.FeatureName.orig p_n) (g p_v), hcvr.origV p_v) ∧
      m = hcfi.cfIntermediateN_f p_n p_v n f ∧
      vs = vs_raw.map hcvr.origV) ∨
    -- f_interToFeat
    (∃ p_n p_v n vs_raw fs v f, ((p_n, p_v), n, vs_raw, fs) ∈ Δ_f ∧ v ∈ vs_raw ∧ f ∈ fs ∧
      p = (hcfi.cfIntermediateN_f p_n p_v n f, hcvr.origV v) ∧
      m = hcnm.granularN (Feature.FeatureName.featured n f) (g v) ∧
      vs = ({v} : Finset V).map hcvr.origV) ∨
    -- f_interFeatToInter (back-edge)
    (∃ p_n p_v n vs_raw fs u f, ((p_n, p_v), n, vs_raw, fs) ∈ Δ_f ∧ u ∈ vs_raw ∧ f ∈ fs ∧
      p = (hcfi.cfIntermediateN_f p_n p_v n f, hcvr.origV u) ∧
      m = hcfi.cfIntermediateN p_n p_v n ∧
      vs = ({u} : Finset V).map hcvr.origV) ∨
    -- a_depToInter
    (∃ p_n p_v f n vs_raw fs, (((p_n, p_v), f), n, vs_raw, fs) ∈ Δ_a ∧
      p = (hcnm.granularN (Feature.FeatureName.featured p_n f) (g p_v), hcvr.origV p_v) ∧
      m = hcfi.cfIntermediateN p_n p_v n ∧
      vs = vs_raw.map hcvr.origV) ∨
    -- a_interToOrig
    (∃ p_n p_v f_dep n vs_raw fs v, (((p_n, p_v), f_dep), n, vs_raw, fs) ∈ Δ_a ∧ v ∈ vs_raw ∧
      p = (hcfi.cfIntermediateN p_n p_v n, hcvr.origV v) ∧
      m = hcnm.granularN (Feature.FeatureName.orig n) (g v) ∧
      vs = ({v} : Finset V).map hcvr.origV) ∨
    -- a_depToInterFeat
    (∃ p_n p_v f_dep n vs_raw fs f', (((p_n, p_v), f_dep), n, vs_raw, fs) ∈ Δ_a ∧ f' ∈ fs ∧
      p = (hcnm.granularN (Feature.FeatureName.featured p_n f_dep) (g p_v), hcvr.origV p_v) ∧
      m = hcfi.cfIntermediateN_a p_n p_v f_dep n f' ∧
      vs = vs_raw.map hcvr.origV) ∨
    -- a_interToFeat
    (∃ p_n p_v f_dep n vs_raw fs v f', (((p_n, p_v), f_dep), n, vs_raw, fs) ∈ Δ_a ∧
      v ∈ vs_raw ∧ f' ∈ fs ∧
      p = (hcfi.cfIntermediateN_a p_n p_v f_dep n f', hcvr.origV v) ∧
      m = hcnm.granularN (Feature.FeatureName.featured n f') (g v) ∧
      vs = ({v} : Finset V).map hcvr.origV) ∨
    -- a_interFeatToInter (back-edge)
    (∃ p_n p_v f_dep n vs_raw fs u f', (((p_n, p_v), f_dep), n, vs_raw, fs) ∈ Δ_a ∧
      u ∈ vs_raw ∧ f' ∈ fs ∧
      p = (hcfi.cfIntermediateN_a p_n p_v f_dep n f', hcvr.origV u) ∧
      m = hcfi.cfIntermediateN p_n p_v n ∧
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
      obtain ⟨hp, hm, hvs⟩ := hmem
      subst hp; subst hm; subst hvs
      exact ⟨n, v, f, hR, hsupp, rfl, rfl, rfl⟩
    · exact absurd hmem (Finset.notMem_empty _)
  · -- f_depToInter
    right; left
    obtain ⟨⟨⟨p_n, p_v⟩, n, vs_raw, fs⟩, hdep, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hp, hm, hvs⟩ := heq
    subst hp; subst hm; subst hvs
    exact ⟨p_n, p_v, n, vs_raw, fs, hdep, rfl, rfl, rfl⟩
  · -- f_interToOrig
    right; right; left
    obtain ⟨⟨⟨p_n, p_v⟩, n, vs_raw, fs⟩, hdep, v, hv, heq⟩ := h
    simp only at hv
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hp, hm, hvs⟩ := heq
    subst hp; subst hm; subst hvs
    exact ⟨p_n, p_v, n, vs_raw, fs, v, hdep, hv, rfl, rfl, rfl⟩
  · -- f_depToInterFeat
    right; right; right; left
    obtain ⟨⟨⟨p_n, p_v⟩, n, vs_raw, fs⟩, hdep, f, hf, heq⟩ := h
    simp only at hf
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hp, hm, hvs⟩ := heq
    subst hp; subst hm; subst hvs
    exact ⟨p_n, p_v, n, vs_raw, fs, f, hdep, hf, rfl, rfl, rfl⟩
  · -- f_interToFeat
    right; right; right; right; left
    obtain ⟨⟨⟨p_n, p_v⟩, n, vs_raw, fs⟩, hdep, v, hv, f, hf, heq⟩ := h
    simp only at hv hf
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hp, hm, hvs⟩ := heq
    subst hp; subst hm; subst hvs
    exact ⟨p_n, p_v, n, vs_raw, fs, v, f, hdep, hv, hf, rfl, rfl, rfl⟩
  · -- f_interFeatToInter
    right; right; right; right; right; left
    obtain ⟨⟨⟨p_n, p_v⟩, n, vs_raw, fs⟩, hdep, f, hf, u, hu, heq⟩ := h
    simp only at hf hu
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hp, hm, hvs⟩ := heq
    subst hp; subst hm; subst hvs
    exact ⟨p_n, p_v, n, vs_raw, fs, u, f, hdep, hu, hf, rfl, rfl, rfl⟩
  · -- a_depToInter
    right; right; right; right; right; right; left
    obtain ⟨⟨⟨⟨p_n, p_v⟩, f⟩, n, vs_raw, fs⟩, hdep, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hp, hm, hvs⟩ := heq
    subst hp; subst hm; subst hvs
    exact ⟨p_n, p_v, f, n, vs_raw, fs, hdep, rfl, rfl, rfl⟩
  · -- a_interToOrig
    right; right; right; right; right; right; right; left
    obtain ⟨⟨⟨⟨p_n, p_v⟩, f⟩, n, vs_raw, fs⟩, hdep, v, hv, heq⟩ := h
    simp only at hv
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hp, hm, hvs⟩ := heq
    subst hp; subst hm; subst hvs
    exact ⟨p_n, p_v, f, n, vs_raw, fs, v, hdep, hv, rfl, rfl, rfl⟩
  · -- a_depToInterFeat
    right; right; right; right; right; right; right; right; left
    obtain ⟨⟨⟨⟨p_n, p_v⟩, f⟩, n, vs_raw, fs⟩, hdep, f', hf', heq⟩ := h
    simp only at hf'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hp, hm, hvs⟩ := heq
    subst hp; subst hm; subst hvs
    exact ⟨p_n, p_v, f, n, vs_raw, fs, f', hdep, hf', rfl, rfl, rfl⟩
  · -- a_interToFeat
    right; right; right; right; right; right; right; right; right; left
    obtain ⟨⟨⟨⟨p_n, p_v⟩, f⟩, n, vs_raw, fs⟩, hdep, v, hv, f', hf', heq⟩ := h
    simp only at hv hf'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hp, hm, hvs⟩ := heq
    subst hp; subst hm; subst hvs
    exact ⟨p_n, p_v, f, n, vs_raw, fs, v, f', hdep, hv, hf', rfl, rfl, rfl⟩
  · -- a_interFeatToInter
    right; right; right; right; right; right; right; right; right; right
    obtain ⟨⟨⟨⟨p_n, p_v⟩, f⟩, n, vs_raw, fs⟩, hdep, f', hf', u, hu, heq⟩ := h
    simp only at hf' hu
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hp, hm, hvs⟩ := heq
    subst hp; subst hm; subst hvs
    exact ⟨p_n, p_v, f, n, vs_raw, fs, u, f', hdep, hu, hf', rfl, rfl, rfl⟩

end PackageCalculus.Composition
