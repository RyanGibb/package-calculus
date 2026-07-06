import PackageCalculus.Extensions.Feature.Reduction.Completeness
import PackageCalculus.Extensions.Feature.Reduction.Soundness

namespace PackageCalculus.Feature

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
  {F : Type*} [DecidableEq F] [Fintype F]
variable {N' : Type*} [DecidableEq N'] [hfn : HasFeatureNames N F N']

/-! ## Computable inverse helpers -/

def tryInvPkg (p : Package N' V) : Option (Package N V) :=
  match hfn.tryOrigN p.1 with
  | some n => some (n, p.2)
  | none => none

attribute [local simp] HasFeatureNames.tryOrigN_origN

omit [DecidableEq N] [DecidableEq V] [DecidableEq F] [Fintype F] [DecidableEq N'] in
private theorem tryInvPkg_embed (p : Package N V) :
    tryInvPkg (hfn := hfn) (embedPkg F p) = some p := by
  simp [tryInvPkg, embedPkg, hfn.tryOrigN_origN]

omit [DecidableEq N] [DecidableEq V] [DecidableEq F] [Fintype F] [DecidableEq N'] in
theorem tryInvPkg_some {p' : Package N' V} {p : Package N V}
    (h : p ∈ tryInvPkg (hfn := hfn) p') : embedPkg F p = p' := by
  obtain ⟨n', v'⟩ := p'
  obtain ⟨n, v⟩ := p
  simp only [tryInvPkg, Option.mem_def, embedPkg] at h ⊢
  generalize htn : hfn.tryOrigN n' = on at h
  match on with
  | some n₀ =>
    simp at h; obtain ⟨rfl, rfl⟩ := h
    show (hfn.origN n₀, v') = (n', v')
    rw [hfn.tryOrigN_some _ _ htn]
  | none => simp at h

omit [DecidableEq N] [DecidableEq V] [DecidableEq F] [Fintype F] [DecidableEq N'] in
private theorem tryInvPkg_inj :
    ∀ a a' (b : Package N V), b ∈ tryInvPkg (hfn := hfn) a → b ∈ tryInvPkg (hfn := hfn) a' → a = a' := by
  intro a a' b ha ha'
  exact (tryInvPkg_some ha).symm.trans (tryInvPkg_some ha')

/-! ## Lift functions -/

/-- Lift an extended-space repository back to the original space. -/
def liftReal (R' : Real N' V) : Real N V :=
  R'.filterMap (tryInvPkg (hfn := hfn)) tryInvPkg_inj

/-- Lift an extended-space resolution back to a feature resolution.
    Each original package is paired with the set of features active for it. -/
def liftResolution (S' : Finset (Package N' V)) :
    Finset (Package N V × Finset F) :=
  (S'.filterMap (tryInvPkg (hfn := hfn)) tryInvPkg_inj).image
    (fun p => (p, Finset.univ.filter (fun f => (hfn.featuredN p.1 f, p.2) ∈ S')))

/-! ## Membership lemmas -/

omit [DecidableEq N] [DecidableEq V] [DecidableEq F] [Fintype F] [DecidableEq N'] in
theorem mem_liftReal {R' : Real N' V} {p : Package N V} :
    p ∈ liftReal (hfn := hfn) R' ↔ embedPkg F p ∈ R' := by
  simp only [liftReal, Finset.mem_filterMap]
  constructor
  · rintro ⟨p', hp', hinv⟩
    exact (tryInvPkg_some hinv) ▸ hp'
  · intro hp
    exact ⟨embedPkg F p, hp, by rw [tryInvPkg_embed]⟩

theorem mem_liftResolution' {S' : Finset (Package N' V)}
    {n : N} {v : V} (h : (hfn.origN n, v) ∈ S') :
    ((n, v), Finset.univ.filter (fun f => (hfn.featuredN n f, v) ∈ S')) ∈
      liftResolution (hfn := hfn) S' := by
  simp only [liftResolution, Finset.mem_image, Finset.mem_filterMap]
  exact ⟨(n, v), ⟨(hfn.origN n, v), h, by simp [tryInvPkg, hfn.tryOrigN_origN]⟩, rfl⟩

theorem liftResolution_elim {S' : Finset (Package N' V)}
    {pfs : Package N V × Finset F} (h : pfs ∈ liftResolution (hfn := hfn) S') :
    ∃ n v, (hfn.origN n, v) ∈ S' ∧
      pfs = ((n, v), Finset.univ.filter (fun f => (hfn.featuredN n f, v) ∈ S')) := by
  simp only [liftResolution, Finset.mem_image, Finset.mem_filterMap] at h
  obtain ⟨⟨n, v⟩, ⟨p', hp', hinv⟩, rfl⟩ := h
  have heq := tryInvPkg_some hinv
  simp only [embedPkg] at heq
  refine ⟨n, v, ?_, rfl⟩
  exact heq ▸ hp'

/-! ## Lifting the support and dependency relations

`featureDeps` emits five families of edges, distinguished by whether the
depender and dependee names are `origN` or `featuredN`:

* (origN, origN): a no-feature parameterised dependency (carried whole);
* (origN, featuredN): one edge per required feature of a featured
  parameterised dependency — the feature set is reassembled by `gatherFs`;
* (featuredN, origN): either a no-feature additional dependency or the
  automatic base requirement of a grounded support fact (these *alias*; the
  overlap is subtracted via `baseDeps`, computed from the lifted repository
  and support);
* (featuredN, featuredN): one edge per required feature of a featured
  additional dependency — reassembled by `gatherAFs`.

The support relation itself is recovered from the reduced repository: featured
packages `(featuredN n f, v)` appear there exactly for grounded support facts. -/

/-- Decode a featured package back to a support fact. -/
def tryInvSupp (p : Package N' V) : Option (Package N V × F) :=
  (hfn.tryFeaturedN p.1).map (fun q => ((q.1, p.2), q.2))

/-- Lift a reduced repository back to a support relation. -/
def liftSupport (R' : Real N' V) : Support N V F :=
  R'.biUnion (fun p => (tryInvSupp (hfn := hfn) p).toFinset)

/-- Reassemble the required-feature set of a featured parameterised dependency
as the set of features whose edge is present. -/
def gatherFs (Δ' : DepRel N' V) (p : Package N V) (n : N) (vs : Finset V) :
    Finset F :=
  Finset.univ.filter (fun f => (embedPkg F p, hfn.featuredN n f, vs) ∈ Δ')

/-- Invert a no-feature parameterised edge (origN depender, origN dependee). -/
def tryInvDepF0 (e : Package N' V × N' × Finset V) :
    Option (Package N V × N × Finset V × Finset F) :=
  match hfn.tryOrigN e.1.1, hfn.tryOrigN e.2.1 with
  | some p₁, some n => some ((p₁, e.1.2), n, e.2.2, ∅)
  | _, _ => none

/-- Invert a featured parameterised edge (origN depender, featuredN dependee),
reassembling the feature set via `gatherFs`. -/
def tryInvDepF1 (Δ' : DepRel N' V) (e : Package N' V × N' × Finset V) :
    Option (Package N V × N × Finset V × Finset F) :=
  match hfn.tryOrigN e.1.1, hfn.tryFeaturedN e.2.1 with
  | some p₁, some (n, _) =>
    some ((p₁, e.1.2), n, e.2.2, gatherFs Δ' (p₁, e.1.2) n e.2.2)
  | _, _ => none

/-- Lift a core dependency relation back to a feature dependency relation. -/
def liftDepsF (Δ' : DepRel N' V) : FeatDepRel N V F :=
  Δ'.biUnion (fun e =>
    (tryInvDepF0 (hfn := hfn) e).toFinset ∪ (tryInvDepF1 Δ' e).toFinset)

/-- Reassemble the required-feature set of a featured additional dependency as
the set of features whose edge is present. -/
def gatherAFs (Δ' : DepRel N' V) (n : N) (v : V) (f : F) (m : N) (vs : Finset V) :
    Finset F :=
  Finset.univ.filter (fun f' => ((hfn.featuredN n f, v), hfn.featuredN m f', vs) ∈ Δ')

/-- Invert a no-feature additional edge (featuredN depender, origN dependee).
Note this also captures the automatic base requirements of grounded support
facts, which alias with them; `liftDepsA` subtracts those. -/
def tryInvDepA0 (e : Package N' V × N' × Finset V) :
    Option ((Package N V × F) × N × Finset V × Finset F) :=
  match hfn.tryFeaturedN e.1.1, hfn.tryOrigN e.2.1 with
  | some (n, f), some m => some (((n, e.1.2), f), m, e.2.2, ∅)
  | _, _ => none

/-- Invert a featured additional edge (featuredN depender, featuredN dependee),
reassembling the feature set via `gatherAFs`. -/
def tryInvDepA1 (Δ' : DepRel N' V) (e : Package N' V × N' × Finset V) :
    Option ((Package N V × F) × N × Finset V × Finset F) :=
  match hfn.tryFeaturedN e.1.1, hfn.tryFeaturedN e.2.1 with
  | some (n, f), some (m, _) =>
    some (((n, e.1.2), f), m, e.2.2, gatherAFs Δ' n e.1.2 f m e.2.2)
  | _, _ => none

/-- Lift a core dependency relation back to an additional-dependency relation,
*before* subtracting the automatic base requirements. -/
def liftDepsARaw (Δ' : DepRel N' V) : AddlDepRel N V F :=
  Δ'.biUnion (fun e =>
    (tryInvDepA0 (hfn := hfn) e).toFinset ∪ (tryInvDepA1 Δ' e).toFinset)

/-- The automatic base requirements induced by a support relation over a
repository: `⟨⟨n,v⟩,f⟩ → n ∋ {v}` for every grounded support fact. -/
def baseDeps (R : Real N V) (support : Support N V F) : AddlDepRel N V F :=
  support.biUnion (fun s => if s.1 ∈ R then {(s, s.1.1, {s.1.2}, ∅)} else ∅)

/-- Lift back to an additional-dependency relation: the raw lift minus the base
requirements recomputed from the lifted repository and support. -/
def liftDepsA (R' : Real N' V) (Δ' : DepRel N' V) : AddlDepRel N V F :=
  liftDepsARaw Δ' \ baseDeps (liftReal (hfn := hfn) R') (liftSupport (hfn := hfn) R')

end PackageCalculus.Feature
