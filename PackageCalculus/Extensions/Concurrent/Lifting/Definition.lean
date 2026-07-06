import PackageCalculus.Extensions.Concurrent.Reduction.Completeness
import PackageCalculus.Extensions.Concurrent.Reduction.Soundness

namespace PackageCalculus.Concurrent

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {G : Type*} [DecidableEq G]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

private def embedPkgFn (g : V → G) : Package N V → Package N' V' :=
  fun p => (hcnm.granularN p.1 (g p.2), hcvr.origV p.2)

theorem embedPkgFn_injective (g : V → G) :
    Function.Injective (embedPkgFn g : Package N V → Package N' V') := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [embedPkgFn, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have ⟨hn, _⟩ := hcnm.granularN_injective h1
  exact Prod.ext hn (hcvr.origV.injective h2)

private def tryInvPkg (g : V → G) (p' : Package N' V') : Option (Package N V) :=
  match hcvr.tryOrigV p'.2 with
  | some v =>
    match hcnm.tryGranularN p'.1 with
    | some (n, g') => if g v = g' then some (n, v) else none
    | none => none
  | none => none

theorem tryInvPkg_embed (g : V → G) (p : Package N V) :
    tryInvPkg g (embedPkg g p) = some p := by
  simp only [tryInvPkg, embedPkg, hcvr.tryOrigV_origV, hcnm.tryGranularN_granularN, ite_true]

theorem tryInvPkg_some (g : V → G) {p' : Package N' V'} {p : Package N V}
    (h : p ∈ tryInvPkg g p') : embedPkg g p = p' := by
  obtain ⟨n, v⟩ := p; obtain ⟨n', v'⟩ := p'
  simp only [tryInvPkg, Option.mem_def] at h
  generalize hv : hcvr.tryOrigV v' = ov at h
  generalize hg : hcnm.tryGranularN n' = og at h
  match ov, og with
  | some v₀, some ng =>
    simp only at h
    split at h
    · rename_i heq_g
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [embedPkg, Prod.mk.injEq]
      exact ⟨by rw [heq_g]; exact hcnm.tryGranularN_some _ _ hg,
             hcvr.tryOrigV_some _ _ hv⟩
    · simp at h
  | some _, none => simp at h
  | none, _ => simp at h

private theorem tryInvPkg_inj (g : V → G) :
    ∀ a a' (b : Package N V), b ∈ tryInvPkg g a → b ∈ tryInvPkg g a' → a = a' := by
  intro a a' b ha ha'
  exact (tryInvPkg_some g ha).symm.trans (tryInvPkg_some g ha')

/-! ## Lift functions -/

def liftReal (g : V → G) (R' : Real N' V') : Real N V :=
  R'.filterMap (tryInvPkg g) (tryInvPkg_inj g)

def liftResolution (g : V → G) (S' : Finset (Package N' V')) :
    Finset (Package N V) :=
  S'.filterMap (tryInvPkg g) (tryInvPkg_inj g)

/-! ## Membership lemmas -/

theorem mem_liftReal {g : V → G} {R' : Real N' V'} {p : Package N V} :
    p ∈ liftReal g R' ↔ embedPkg g p ∈ R' := by
  simp only [liftReal, Finset.mem_filterMap]
  constructor
  · rintro ⟨_, hp', hinv⟩
    exact (tryInvPkg_some g (Option.mem_def.mpr hinv)) ▸ hp'
  · exact fun hp => ⟨_, hp, Option.mem_def.mpr (tryInvPkg_embed g p)⟩

theorem mem_liftResolution {g : V → G} {S' : Finset (Package N' V')} {p : Package N V} :
    p ∈ liftResolution g S' ↔ embedPkg g p ∈ S' := by
  simp only [liftResolution, Finset.mem_filterMap]
  constructor
  · rintro ⟨_, hp', hinv⟩
    exact (tryInvPkg_some g (Option.mem_def.mpr hinv)) ▸ hp'
  · exact fun hp => ⟨_, hp, Option.mem_def.mpr (tryInvPkg_embed g p)⟩

/-! ## Lifting the dependency relation

`concurrentDeps` sends one concurrent entry `((n, v), m, vs)` to a family of
core edges whose shape depends on the granularity structure of `vs`:

* a *direct* entry (`vs` non-empty, all versions of the same granularity)
  yields a single edge carrying the full `vs`;
* an *empty* entry (`vs = ∅`) yields a single depender→intermediate edge
  carrying `∅`;
* a *split* entry (`vs` spans ≥2 granularities) yields a depender→intermediate
  edge plus one intermediate→dependee edge per granularity group.

We recover each entry from a canonical family of edges: direct entries from
their single edge, empty entries from their depender→intermediate edge, and
split entries from their intermediate→dependee edges, reassembling `vs` as the
union of the granularity groups (`gatherVs`). -/

/-- Injectivity side-condition for `filterMap`ing `tryOrigV`. The unused
`g` argument only serves to pin the granularity type `G`. -/
private theorem tryOrigV_filterMap_inj (_g : V → G) :
    ∀ (a a' : V') (b : V), b ∈ hcvr.tryOrigV a → b ∈ hcvr.tryOrigV a' → a = a' := by
  intro a a' b ha ha'
  have h1 := hcvr.tryOrigV_some _ _ (Option.mem_def.mp ha)
  have h2 := hcvr.tryOrigV_some _ _ (Option.mem_def.mp ha')
  exact h1.symm.trans h2

/-- Decode a version set of `origV`-versions back to the underlying `Finset V`.
The unused `g` argument only serves to pin the granularity type `G`. -/
def decodeVS (g : V → G) (vs' : Finset V') : Finset V :=
  vs'.filterMap hcvr.tryOrigV (tryOrigV_filterMap_inj g)

theorem decodeVS_map_origV (g : V → G) (vs : Finset V) :
    decodeVS g (vs.map hcvr.origV) = vs := by
  ext x
  simp only [decodeVS, Finset.mem_filterMap, Finset.mem_map]
  constructor
  · rintro ⟨y, ⟨v, hv, rfl⟩, hxy⟩
    rw [hcvr.tryOrigV_origV] at hxy
    obtain rfl := Option.some.inj hxy
    exact hv
  · intro hx
    exact ⟨hcvr.origV x, ⟨x, hx, rfl⟩, hcvr.tryOrigV_origV x⟩

/-- Reassemble the version set of a split entry as the union, over all
intermediate→dependee edges leaving the intermediate name `I`, of their
(decoded) version groups. -/
def gatherVs (g : V → G) (Δ' : DepRel N' V') (I : N') : Finset V :=
  (Δ'.filter (fun e => e.1.1 = I)).biUnion (fun e => decodeVS g e.2.2)

/-- Try to invert a *direct* edge: both endpoints granular, versions all
`origV`, granularity-consistent with `g`, and non-empty. -/
def tryInvDirect (g : V → G) (e : Package N' V' × N' × Finset V') :
    Option (Package N V × N × Finset V) :=
  match hcnm.tryGranularN e.1.1, hcvr.tryOrigV e.1.2, hcnm.tryGranularN e.2.1 with
  | some (n, gv), some v, some (m, mt) =>
    let vs := decodeVS g e.2.2
    if vs.map hcvr.origV = e.2.2 ∧ gv = g v ∧ vs.Nonempty ∧ (∀ u ∈ vs, g u = mt) then
      some ((n, v), m, vs)
    else none
  | _, _, _ => none

/-- Try to invert an *empty* edge: granular depender, intermediate dependee,
empty version set. -/
def tryInvEmpty (g : V → G) (e : Package N' V' × N' × Finset V') :
    Option (Package N V × N × Finset V) :=
  match hcnm.tryGranularN e.1.1, hcvr.tryOrigV e.1.2, hcnm.tryIntermediateN e.2.1 with
  | some (n, gv), some v, some (n2, v2, m) =>
    if e.2.2 = ∅ ∧ gv = g v ∧ n2 = n ∧ v2 = v then some ((n, v), m, ∅) else none
  | _, _, _ => none

/-- Try to invert a *split* intermediate→dependee edge: decode the intermediate
name in the depender to `(n, v, m)`, and reassemble `vs` via `gatherVs`. -/
def tryInvSplit (g : V → G) (Δ' : DepRel N' V') (e : Package N' V' × N' × Finset V') :
    Option (Package N V × N × Finset V) :=
  (hcnm.tryIntermediateN e.1.1).map (fun p => ((p.1, p.2.1), p.2.2, gatherVs g Δ' e.1.1))

/-- Lift a core dependency relation back to a concurrent one. -/
def liftDeps (g : V → G) (Δ' : DepRel N' V') : DepRel N V :=
  Δ'.biUnion (fun e =>
    (tryInvDirect g e).toFinset ∪ (tryInvEmpty g e).toFinset ∪ (tryInvSplit g Δ' e).toFinset)

end PackageCalculus.Concurrent
