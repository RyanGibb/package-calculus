import PackageCalculus.Extensions.Conflict.Reduction.Completeness
import PackageCalculus.Extensions.Conflict.Reduction.Soundness

namespace PackageCalculus.Conflict

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcn : HasConflictNames N V N'] [hcv : HasConflictVersions V V']

private def embedPkgFn : Package N V → Package N' V' :=
  fun p => (hcn.origN p.1, hcv.origV p.2)

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
private theorem embedPkgFn_eq_embedPkg : (embedPkgFn : Package N V → Package N' V') = embedPkg :=
  rfl

def embedDepFn : Package N V × N × Finset V → Package N' V' × N' × Finset V' :=
  fun ⟨p, m, vs⟩ => ((hcn.origN p.1, hcv.origV p.2), hcn.origN m, vs.map hcv.origV)

def conflictDepFn : Package N V × N × Finset V → Package N' V' × N' × Finset V' :=
  fun ⟨p, n, vs⟩ => ((hcn.origN p.1, hcv.origV p.2), hcn.syntheticN n vs, {hcv.oneV})

/-! ## Computable inverse helpers -/

/-- Try to invert `embedPkgFn` on a single element. -/
private def tryInvPkg (p : Package N' V') : Option (Package N V) :=
  match hcn.tryOrigN p.1, hcv.tryOrigV p.2 with
  | some n, some v => some (n, v)
  | _, _ => none

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
private theorem tryInvPkg_embed (p : Package N V) :
    tryInvPkg (embedPkgFn p) = some p := by
  simp [tryInvPkg, embedPkgFn, hcn.tryOrigN_origN, hcv.tryOrigV_origV]

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
private theorem tryInvPkg_some {p' : Package N' V'} {p : Package N V}
    (h : p ∈ tryInvPkg p') : embedPkgFn p = p' := by
  obtain ⟨n', v'⟩ := p'
  obtain ⟨n, v⟩ := p
  simp only [tryInvPkg, Option.mem_def, embedPkgFn] at h ⊢
  generalize htn : hcn.tryOrigN n' = on at h
  generalize htv : hcv.tryOrigV v' = ov at h
  match on, ov with
  | some n₀, some v₀ =>
    simp at h; obtain ⟨rfl, rfl⟩ := h
    show (hcn.origN n₀, hcv.origV v₀) = (n', v')
    rw [hcn.tryOrigN_some _ _ htn, hcv.tryOrigV_some _ _ htv]
  | some _, none => simp at h
  | none, _ => simp at h

omit [DecidableEq N] [DecidableEq V] [DecidableEq N'] [DecidableEq V'] in
private theorem tryInvPkg_inj :
    ∀ a a' (b : Package N V), b ∈ tryInvPkg a → b ∈ tryInvPkg a' → a = a' := by
  intro a a' b ha ha'
  exact (tryInvPkg_some ha).symm.trans (tryInvPkg_some ha')

/-- The injectivity side-condition for `filterMap`ing `tryOrigV`. -/
private theorem tryOrigV_filterMap_inj :
    ∀ (a a' : V') (b : V), b ∈ hcv.tryOrigV a → b ∈ hcv.tryOrigV a' → a = a' := by
  intro a a' b ha ha'
  have h1 := hcv.tryOrigV_some _ _ (Option.mem_def.mp ha)
  have h2 := hcv.tryOrigV_some _ _ (Option.mem_def.mp ha')
  exact h1.symm.trans h2

/-- `filterMap tryOrigV` is a left inverse of `map origV`. -/
private theorem filterMap_tryOrigV_map_origV (vs : Finset V) :
    (vs.map hcv.origV).filterMap hcv.tryOrigV tryOrigV_filterMap_inj = vs := by
  ext x
  simp only [Finset.mem_filterMap, Finset.mem_map]
  constructor
  · rintro ⟨y, ⟨v, hv, rfl⟩, hxy⟩
    rw [hcv.tryOrigV_origV] at hxy
    obtain rfl := Option.some.inj hxy
    exact hv
  · intro hx
    exact ⟨hcv.origV x, ⟨x, hx, rfl⟩, hcv.tryOrigV_origV x⟩

/-- Try to invert `embedDepFn` on a single element. -/
private def tryInvDep (d : Package N' V' × N' × Finset V') :
    Option (Package N V × N × Finset V) :=
  match hcn.tryOrigN d.1.1, hcv.tryOrigV d.1.2, hcn.tryOrigN d.2.1 with
  | some pn, some pv, some m =>
    let vs := d.2.2.filterMap hcv.tryOrigV tryOrigV_filterMap_inj
    if vs.map hcv.origV = d.2.2 then
      some ((pn, pv), m, vs)
    else none
  | _, _, _ => none

private theorem tryInvDep_some {d : Package N' V' × N' × Finset V'}
    {c : Package N V × N × Finset V} (h : c ∈ tryInvDep d) : embedDepFn c = d := by
  obtain ⟨⟨dn, dv⟩, dm, dvs⟩ := d
  simp only [tryInvDep, Option.mem_def] at h
  revert h
  cases hn : hcn.tryOrigN dn <;> cases hv : hcv.tryOrigV dv <;> cases hm : hcn.tryOrigN dm <;>
    simp only [reduceCtorEq, false_implies]
  split
  · rename_i hmap
    intro h
    obtain rfl := Option.some.inj h
    simp only [embedDepFn]
    rw [hcn.tryOrigN_some _ _ hn, hcv.tryOrigV_some _ _ hv, hcn.tryOrigN_some _ _ hm, hmap]
  · simp

private theorem tryInvDep_embedDepFn (c : Package N V × N × Finset V) :
    tryInvDep (embedDepFn c) = some c := by
  obtain ⟨⟨pn, pv⟩, m, vs⟩ := c
  simp only [tryInvDep, embedDepFn, hcn.tryOrigN_origN, hcv.tryOrigV_origV,
    filterMap_tryOrigV_map_origV, if_pos]

private theorem tryInvDep_inj :
    ∀ a a' (b : Package N V × N × Finset V),
      b ∈ tryInvDep a → b ∈ tryInvDep a' → a = a' := by
  intro a a' b h1 h2
  rw [← tryInvDep_some h1, ← tryInvDep_some h2]

/-- Try to invert `conflictDepFn` on a single element. -/
private def tryInvConflict (d : Package N' V' × N' × Finset V') :
    Option (Package N V × N × Finset V) :=
  match tryInvPkg d.1, hcn.trySyntheticN d.2.1 with
  | some p, some (n, vs) => if d.2.2 = {hcv.oneV} then some (p, n, vs) else none
  | _, _ => none

private theorem tryInvConflict_some {d : Package N' V' × N' × Finset V'}
    {c : Package N V × N × Finset V} (h : c ∈ tryInvConflict d) : conflictDepFn c = d := by
  obtain ⟨dp, dm, dvs⟩ := d
  simp only [tryInvConflict, Option.mem_def] at h
  revert h
  cases hp : (tryInvPkg dp : Option (Package N V)) <;>
    cases hm : (hcn.trySyntheticN dm : Option (N × Finset V)) <;>
    simp only [reduceCtorEq, false_implies]
  rename_i p nvs
  obtain ⟨n, vs⟩ := nvs
  split
  · rename_i hone
    intro h
    obtain rfl := Option.some.inj h
    simp only [conflictDepFn]
    have hpeq := tryInvPkg_some (Option.mem_def.mpr hp)
    rw [embedPkgFn_eq_embedPkg] at hpeq
    have hmeq := hcn.trySyntheticN_some _ _ hm
    exact Prod.ext hpeq (Prod.ext hmeq hone.symm)
  · simp

private theorem tryInvConflict_conflictDepFn (c : Package N V × N × Finset V) :
    tryInvConflict (conflictDepFn c) = some c := by
  obtain ⟨⟨pn, pv⟩, n, vs⟩ := c
  simp only [tryInvConflict, conflictDepFn, hcn.trySyntheticN_syntheticN, if_pos]
  have : tryInvPkg ((hcn.origN pn, hcv.origV pv) : Package N' V') = some (pn, pv) := by
    have := tryInvPkg_embed (pn, pv)
    rwa [embedPkgFn] at this
  rw [this]

private theorem tryInvConflict_inj :
    ∀ a a' (b : Package N V × N × Finset V),
      b ∈ tryInvConflict a → b ∈ tryInvConflict a' → a = a' := by
  intro a a' b h1 h2
  rw [← tryInvConflict_some h1, ← tryInvConflict_some h2]

/-! ## Lift functions -/

def liftReal (R' : Real N' V') : Real N V :=
  R'.filterMap tryInvPkg tryInvPkg_inj

def liftDeps (Δ' : DepRel N' V') : DepRel N V :=
  Δ'.filterMap tryInvDep tryInvDep_inj

def liftConflicts (Δ' : DepRel N' V') : ConflictRel N V :=
  Δ'.filterMap tryInvConflict tryInvConflict_inj

def liftResolution (S' : Finset (Package N' V')) : Finset (Package N V) :=
  S'.filterMap tryInvPkg tryInvPkg_inj

def conflictLift (R' : Real N' V') (Δ' : DepRel N' V') :
    Real N V × DepRel N V × ConflictRel N V :=
  (liftReal R', liftDeps Δ', liftConflicts Δ')

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

theorem mem_liftDeps {Δ' : DepRel N' V'} {d : Package N V × N × Finset V} :
    d ∈ liftDeps Δ' ↔ embedDepFn d ∈ Δ' := by
  simp only [liftDeps, Finset.mem_filterMap]
  constructor
  · rintro ⟨e, he, hinv⟩
    rw [tryInvDep_some hinv]; exact he
  · intro h
    exact ⟨embedDepFn d, h, tryInvDep_embedDepFn d⟩

theorem mem_liftConflicts {Δ' : DepRel N' V'} {c : Package N V × N × Finset V} :
    c ∈ liftConflicts Δ' ↔ conflictDepFn c ∈ Δ' := by
  simp only [liftConflicts, Finset.mem_filterMap]
  constructor
  · rintro ⟨e, he, hinv⟩
    rw [tryInvConflict_some hinv]; exact he
  · intro h
    exact ⟨conflictDepFn c, h, tryInvConflict_conflictDepFn c⟩

end PackageCalculus.Conflict
