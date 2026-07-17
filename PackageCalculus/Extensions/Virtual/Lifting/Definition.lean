import PackageCalculus.Extensions.Virtual.Reduction.Completeness
import PackageCalculus.Extensions.Virtual.Reduction.Soundness

namespace PackageCalculus.Virtual

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVirtualNames N V N'] [hvv : HasVirtualVersions N V V']

/-! ## Lift functions -/

def embedPkgFn : Package N V → Package N' V' :=
  fun p => (hvn.origN p.1, hvv.origV p.2)

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem embedPkgFn_eq_embedPkg :
    (embedPkgFn : Package N V → Package N' V') = embedPkg :=
  rfl

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem embedPkgFn_injective :
    Function.Injective (embedPkgFn : Package N V → Package N' V') := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [embedPkgFn, Prod.mk.injEq] at h
  exact Prod.ext (hvn.origN.injective h.1) (hvv.origV.injective h.2)

def tryInvPkg (p : Package N' V') : Option (Package N V) :=
  match hvn.tryOrigN p.1, hvv.tryOrigV p.2 with
  | some n, some v => some (n, v)
  | _, _ => none

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem tryInvPkg_embed (p : Package N V) :
    tryInvPkg (embedPkgFn p) = some p := by
  simp [tryInvPkg, embedPkgFn, hvn.tryOrigN_origN, hvv.tryOrigV_origV]

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem tryInvPkg_some {p' : Package N' V'} {p : Package N V}
    (h : p ∈ tryInvPkg p') : embedPkgFn p = p' := by
  obtain ⟨n', v'⟩ := p'; obtain ⟨n, v⟩ := p
  simp only [tryInvPkg, Option.mem_def, embedPkgFn] at h ⊢
  generalize htn : hvn.tryOrigN n' = on at h
  generalize htv : hvv.tryOrigV v' = ov at h
  match on, ov with
  | some n₀, some v₀ =>
    simp at h; obtain ⟨rfl, rfl⟩ := h
    show (hvn.origN n₀, hvv.origV v₀) = (n', v')
    rw [hvn.tryOrigN_some _ _ htn, hvv.tryOrigV_some _ _ htv]
  | some _, none => simp at h
  | none, _ => simp at h

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
private theorem tryInvPkg_inj :
    ∀ a a' (b : Package N V), b ∈ tryInvPkg a → b ∈ tryInvPkg a' → a = a' := by
  intro a a' b ha ha'
  exact (tryInvPkg_some ha).symm.trans (tryInvPkg_some ha')

def liftReal (R' : Real N' V') : Real N V :=
  R'.filterMap tryInvPkg tryInvPkg_inj

def liftResolution (S' : Finset (Package N' V')) : Finset (Package N V) :=
  S'.filterMap tryInvPkg tryInvPkg_inj

/-! ## Membership lemmas -/

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem mem_liftReal {R' : Real N' V'} {p : Package N V} :
    p ∈ liftReal R' ↔ embedPkg p ∈ R' := by
  simp only [liftReal, Finset.mem_filterMap, ← embedPkgFn_eq_embedPkg]
  constructor
  · rintro ⟨_, hp', hinv⟩; exact tryInvPkg_some hinv ▸ hp'
  · exact fun hp => ⟨_, hp, tryInvPkg_embed p⟩

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem mem_liftResolution {S' : Finset (Package N' V')} {p : Package N V} :
    p ∈ liftResolution S' ↔ embedPkg p ∈ S' := by
  simp only [liftResolution, Finset.mem_filterMap, ← embedPkgFn_eq_embedPkg]
  constructor
  · rintro ⟨_, hp', hinv⟩; exact tryInvPkg_some hinv ▸ hp'
  · exact fun hp => ⟨_, hp, tryInvPkg_embed p⟩

/-! ## Lifting the dependency relation

`virtualDeps` sends a no-provider entry to a single edge carrying its whole
version set, and a with-provider entry to a depender→selector edge plus one
selector edge per matching provider (clause 3) and per real direct version
(clause 4). Only the real direct versions survive in recoverable form — the
version set is reassembled from the selector→direct edges (`gatherVS`) — so
the lift lands on `Δ.restrictReal R`, mirroring the Versions retraction. -/

set_option linter.unusedSectionVars false

/-- Injectivity side-condition for `filterMap`ing `tryOrigV`. The unused `R`
argument only serves to pin the name type `N` of the version encoding. -/
private theorem tryOrigV_filterMap_inj (_R : Real N V) :
    ∀ (a a' : V') (b : V), b ∈ hvv.tryOrigV a → b ∈ hvv.tryOrigV a' → a = a' := by
  intro a a' b ha ha'
  have h1 := hvv.tryOrigV_some _ _ (Option.mem_def.mp ha)
  have h2 := hvv.tryOrigV_some _ _ (Option.mem_def.mp ha')
  exact h1.symm.trans h2

/-- Decode a version set of `origV`-versions back to the underlying `Finset V`.
The unused `R` argument only serves to pin the name type `N`. -/
def decodeVS (R : Real N V) (vs' : Finset V') : Finset V :=
  vs'.filterMap hvv.tryOrigV (tryOrigV_filterMap_inj R)

theorem decodeVS_map_origV (R : Real N V) (vs : Finset V) :
    decodeVS R (vs.map hvv.origV) = vs := by
  ext x
  simp only [decodeVS, Finset.mem_filterMap, Finset.mem_map]
  constructor
  · rintro ⟨y, ⟨v, hv, rfl⟩, hxy⟩
    rw [hvv.tryOrigV_origV] at hxy
    obtain rfl := Option.some.inj hxy
    exact hv
  · intro hx
    exact ⟨hvv.origV x, ⟨x, hx, rfl⟩, hvv.tryOrigV_origV x⟩

/-- Invert a *no-provider* edge (orig depender, orig dependee, orig versions),
restricting the decoded version set to real packages. -/
def tryInvDirect (R : Real N V) (e : Package N' V' × N' × Finset V') :
    Option (Package N V × N × Finset V) :=
  match hvn.tryOrigN e.1.1, hvv.tryOrigV e.1.2, hvn.tryOrigN e.2.1 with
  | some pn, some pv, some n =>
    let vs := decodeVS R e.2.2
    if e.2.2 = vs.map hvv.origV then
      some ((pn, pv), n, vs.filter (fun u => (n, u) ∈ R))
    else none
  | _, _, _ => none

/-- The direct versions carried by a selector's out-edge version `v'`: `u` when
`v'` is the provider version `⟨n, u⟩` built from the virtual name `n` itself. -/
def tryGatherV (n : N) (v' : V') : Finset V :=
  match hvv.tryProviderV v' with
  | some (a, u) => if a = n then {u} else ∅
  | none => ∅

/-- Reassemble the real direct versions of a with-provider entry from the
selector→direct edges leaving its selector. -/
def gatherVS (Δ' : DepRel N' V') (p : Package N V) (n : N) : Finset V :=
  Δ'.biUnion (fun e => if e.1.1 = hvn.selectorN p n then tryGatherV n e.1.2 else ∅)

/-- Invert a *with-provider* depender→selector edge, reassembling the (real)
version set via `gatherVS`. -/
def tryInvSelector (Δ' : DepRel N' V') (e : Package N' V' × N' × Finset V') :
    Option (Package N V × N × Finset V) :=
  match hvn.tryOrigN e.1.1, hvv.tryOrigV e.1.2, hvn.trySelectorN e.2.1 with
  | some pn, some pv, some (q, n) =>
    if q = (pn, pv) then some ((pn, pv), n, gatherVS Δ' (pn, pv) n) else none
  | _, _, _ => none

/-- Lift a core dependency relation back to a virtual dependency relation
(up to `restrictReal`; `R` is the already-lifted repository). -/
def liftDeps (R : Real N V) (Δ' : DepRel N' V') : DepRel N V :=
  Δ'.biUnion (fun e => (tryInvDirect R e).toFinset ∪ (tryInvSelector Δ' e).toFinset)

/-- Invert a selector→provider edge to its instantiation triple `(q, n, p)`.
Under `NoSelfProvides` the provider edges are exactly those whose provider
version carries a name other than the selector's dependency name. -/
def tryInvProv (e : Package N' V' × N' × Finset V') :
    Option (Package N V × N × Package N V) :=
  match hvn.trySelectorN e.1.1, hvv.tryProviderV e.1.2 with
  | some (p, n), some (m, w) => if m = n then none else some ((m, w), n, p)
  | _, _ => none

/-- Lift the instantiation of the provides relation from the reduced
dependency relation. -/
def liftProv (Δ' : DepRel N' V') : Finset (Package N V × N × Package N V) :=
  Δ'.biUnion fun e => (tryInvProv e).toFinset

end PackageCalculus.Virtual
