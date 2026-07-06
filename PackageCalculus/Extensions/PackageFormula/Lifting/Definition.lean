import PackageCalculus.Extensions.PackageFormula.Reduction.Completeness
import PackageCalculus.Extensions.PackageFormula.Reduction.Soundness

namespace PackageCalculus.PkgFormula

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hpn : HasPFNames N V N'] [hpv : Conflict.HasConflictVersions V V']

def embedPkgFn : Package N V → Package N' V' :=
  fun p => (hpn.origN p.1, hpv.origV p.2)

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem embedPkgFn_eq_embedPkg : (embedPkgFn : Package N V → Package N' V') = embedPkg :=
  rfl

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem embedPkgFn_injective :
    Function.Injective (embedPkgFn : Package N V → Package N' V') := by
  intro ⟨n₁, v₁⟩ ⟨n₂, v₂⟩ h
  simp only [embedPkgFn, Prod.mk.injEq] at h
  exact Prod.ext (hpn.origN.injective h.1) (hpv.origV.injective h.2)

def tryInvPkg (p : Package N' V') : Option (Package N V) :=
  match hpn.tryOrigN p.1, hpv.tryOrigV p.2 with
  | some n, some v => some (n, v)
  | _, _ => none

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem tryInvPkg_embed (p : Package N V) :
    tryInvPkg (embedPkgFn p) = some p := by
  simp [tryInvPkg, embedPkgFn, hpn.tryOrigN_origN, hpv.tryOrigV_origV]

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
theorem tryInvPkg_some {p' : Package N' V'} {p : Package N V}
    (h : p ∈ tryInvPkg p') : embedPkgFn p = p' := by
  obtain ⟨n', v'⟩ := p'; obtain ⟨n, v⟩ := p
  simp only [tryInvPkg, Option.mem_def, embedPkgFn] at h ⊢
  generalize htn : hpn.tryOrigN n' = on at h
  generalize htv : hpv.tryOrigV v' = ov at h
  match on, ov with
  | some n₀, some v₀ =>
    simp at h; obtain ⟨rfl, rfl⟩ := h
    show (hpn.origN n₀, hpv.origV v₀) = (n', v')
    rw [hpn.tryOrigN_some _ _ htn, hpv.tryOrigV_some _ _ htv]
  | some _, none => simp at h
  | none, _ => simp at h

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
private theorem tryInvPkg_inj :
    ∀ a a' (b : Package N V), b ∈ tryInvPkg a → b ∈ tryInvPkg a' → a = a' := by
  intro a a' b ha ha'
  exact (tryInvPkg_some ha).symm.trans (tryInvPkg_some ha')

/-! ## Lift functions -/

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

/-! ## Lifting the dependency relation onto the atom normal form

Per depender, the encoding emits one edge per NNF atom — positive literals
carry their version set, negative literals and disjunctions are named
synthetically — plus guard edges (real dependers, version `{0}`) and nested
edges (disjunct-witness dependers). The decoders below recognise exactly the
atom edges of `embedPkg`-shaped dependers. -/

/-- The edge a top-level atom of depender `p` contributes to the encoding. -/
def atomEdge (p : Package N' V') : Atom N V → Package N' V' × N' × Finset V'
  | .pos n vs => (p, hpn.origN n, embedVS vs)
  | .neg n vs => (p, hpn.syntheticN n vs, {hpv.oneV})
  | .disj ψ_L ψ_R => (p, hpn.disjunctN ψ_L ψ_R, {hpv.zeroV, hpv.oneV})

/-- The depender of an atom edge is the given package. -/
theorem atomEdge_fst (p : Package N' V') (a : Atom N V) : (atomEdge p a).1 = p := by
  cases a <;> rfl

/-- Injectivity side-condition for `filterMap`ing `tryOrigV`. -/
private theorem tryOrigV_filterMap_inj :
    ∀ (a a' : V') (b : V), b ∈ hpv.tryOrigV a → b ∈ hpv.tryOrigV a' → a = a' := by
  intro a a' b ha ha'
  have h1 := hpv.tryOrigV_some _ _ (Option.mem_def.mp ha)
  have h2 := hpv.tryOrigV_some _ _ (Option.mem_def.mp ha')
  exact h1.symm.trans h2

/-- Decode a version set of `origV`-versions back to the underlying `Finset V`. -/
def decodeVS (vs' : Finset V') : Finset V :=
  vs'.filterMap hpv.tryOrigV tryOrigV_filterMap_inj

theorem decodeVS_embedVS (vs : Finset V) : decodeVS (embedVS (hpv := hpv) vs) = vs := by
  ext x
  simp only [decodeVS, embedVS, Finset.mem_filterMap, Finset.mem_map]
  constructor
  · rintro ⟨y, ⟨v, hv, rfl⟩, hxy⟩
    rw [hpv.tryOrigV_origV] at hxy
    obtain rfl := Option.some.inj hxy
    exact hv
  · intro hx
    exact ⟨hpv.origV x, ⟨x, hx, rfl⟩, hpv.tryOrigV_origV x⟩

/-- Invert a positive-literal edge (orig depender, orig dependee, orig versions). -/
def tryInvPos (e : Package N' V' × N' × Finset V') : Option (Package N V × Atom N V) :=
  match hpn.tryOrigN e.1.1, hpv.tryOrigV e.1.2, hpn.tryOrigN e.2.1 with
  | some pn, some pv, some n =>
    let vs := decodeVS e.2.2
    if e.2.2 = embedVS vs then some ((pn, pv), .pos n vs) else none
  | _, _, _ => none

/-- Invert a negative-literal edge; the version-set guard `{1}` excludes the
guard edges (version `{0}`) that negative literals attach to real packages. -/
def tryInvNeg (e : Package N' V' × N' × Finset V') : Option (Package N V × Atom N V) :=
  match hpn.tryOrigN e.1.1, hpv.tryOrigV e.1.2, hpn.trySyntheticN e.2.1 with
  | some pn, some pv, some (n, vs) =>
    if e.2.2 = {hpv.oneV} then some ((pn, pv), .neg n vs) else none
  | _, _, _ => none

/-- Invert a disjunction edge; the synthetic name carries the subformulas. -/
def tryInvDisj (e : Package N' V' × N' × Finset V') : Option (Package N V × Atom N V) :=
  match hpn.tryOrigN e.1.1, hpv.tryOrigV e.1.2, hpn.tryDisjunctN e.2.1 with
  | some pn, some pv, some (ψ_L, ψ_R) =>
    if e.2.2 = {hpv.zeroV, hpv.oneV} then some ((pn, pv), .disj ψ_L ψ_R) else none
  | _, _, _ => none

/-- Lift a core dependency relation back to per-depender NNF atoms. -/
def liftAtoms (Δ' : DepRel N' V') : Finset (Package N V × Atom N V) :=
  Δ'.biUnion (fun e =>
    (tryInvPos e).toFinset ∪ (tryInvNeg e).toFinset ∪ (tryInvDisj e).toFinset)

end PackageCalculus.PkgFormula
