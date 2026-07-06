import PackageCalculus.Extensions.PeerDependency.Reduction.Completeness
import PackageCalculus.Extensions.PeerDependency.Reduction.Soundness
import PackageCalculus.Extensions.Concurrent.Lifting.Definition

namespace PackageCalculus.PeerDep

open PackageCalculus Concurrent

set_option linter.unusedSectionVars false

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {G : Type*} [DecidableEq G]
variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

/-! ## Lift functions -/

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
    tryInvPkg g (Concurrent.embedPkg g p) = some p := by
  simp only [tryInvPkg, Concurrent.embedPkg, hcvr.tryOrigV_origV, hcnm.tryGranularN_granularN,
    ite_true]

theorem tryInvPkg_some (g : V → G) {p' : Package N' V'} {p : Package N V}
    (h : p ∈ tryInvPkg g p') : Concurrent.embedPkg g p = p' := by
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
      simp only [Concurrent.embedPkg, Prod.mk.injEq]
      exact ⟨by rw [heq_g]; exact hcnm.tryGranularN_some _ _ hg,
             hcvr.tryOrigV_some _ _ hv⟩
    · simp at h
  | some _, none => simp at h
  | none, _ => simp at h

private theorem tryInvPkg_inj (g : V → G) :
    ∀ a a' (b : Package N V), b ∈ tryInvPkg g a → b ∈ tryInvPkg g a' → a = a' := by
  intro a a' b ha ha'
  exact (tryInvPkg_some g ha).symm.trans (tryInvPkg_some g ha')

def liftReal (g : V → G) (R' : Real N' V') : Real N V :=
  R'.filterMap (tryInvPkg g) (tryInvPkg_inj g)

def liftResolution (g : V → G) (S' : Finset (Package N' V')) :
    Finset (Package N V) :=
  S'.filterMap (tryInvPkg g) (tryInvPkg_inj g)

/-! ## Membership lemmas -/

theorem mem_liftReal {g : V → G} {R' : Real N' V'} {p : Package N V} :
    p ∈ liftReal g R' ↔ Concurrent.embedPkg g p ∈ R' := by
  simp only [liftReal, Finset.mem_filterMap]
  constructor
  · rintro ⟨_, hp', hinv⟩
    exact (tryInvPkg_some g (Option.mem_def.mpr hinv)) ▸ hp'
  · exact fun hp => ⟨_, hp, Option.mem_def.mpr (tryInvPkg_embed g p)⟩

theorem mem_liftResolution {g : V → G} {S' : Finset (Package N' V')} {p : Package N V} :
    p ∈ liftResolution g S' ↔ Concurrent.embedPkg g p ∈ S' := by
  simp only [liftResolution, Finset.mem_filterMap]
  constructor
  · rintro ⟨_, hp', hinv⟩
    exact (tryInvPkg_some g (Option.mem_def.mpr hinv)) ▸ hp'
  · exact fun hp => ⟨_, hp, Option.mem_def.mpr (tryInvPkg_embed g p)⟩

/-! ## Lifting the dependency and peer relations

`peerDeps` sends the calculus to the core using two kinds of intermediate:
`⟨n,v,m⟩`-intermediates mediate ordinary dependencies, and their edges into
other intermediates carry peer constraints. Unlike the concurrent reduction,
peer edges carry the *whole* version set (no granularity split), so both
relations are recovered edge-locally:

* the original dependency `⟨n,v⟩ → m ∋ vs` is read off the single
  depender→intermediate edge (granular depender, intermediate dependee);
* a peer constraint `⟨o,u⟩ → m ∋ ws` is read off any intermediate→intermediate
  edge, decoding both intermediate names. -/

/-- Invert a depender→intermediate edge to its core dependency. -/
def tryInvDelta (g : V → G) (e : Package N' V' × N' × Finset V') :
    Option (Package N V × N × Finset V) :=
  match hcnm.tryGranularN e.1.1, hcvr.tryOrigV e.1.2, hcnm.tryIntermediateN e.2.1 with
  | some (n, gv), some v, some (n2, v2, m) =>
    let vs := Concurrent.decodeVS g e.2.2
    if e.2.2 = vs.map hcvr.origV ∧ gv = g v ∧ n2 = n ∧ v2 = v then some ((n, v), m, vs) else none
  | _, _, _ => none

/-- Invert an intermediate→intermediate edge to its peer constraint. -/
def tryInvPeer (g : V → G) (e : Package N' V' × N' × Finset V') :
    Option (Package N V × N × Finset V) :=
  match hcnm.tryIntermediateN e.1.1, hcvr.tryOrigV e.1.2, hcnm.tryIntermediateN e.2.1 with
  | some (n, v, o), some u, some (n2, v2, m) =>
    let ws := Concurrent.decodeVS g e.2.2
    if e.2.2 = ws.map hcvr.origV ∧ n2 = n ∧ v2 = v then some ((o, u), m, ws) else none
  | _, _, _ => none

/-- Lift a core dependency relation back to a peer dependency relation. -/
def liftDeps (g : V → G) (Δ' : DepRel N' V') : DepRel N V :=
  Δ'.biUnion (fun e => (tryInvDelta g e).toFinset)

/-- Lift a core dependency relation back to a peer relation. -/
def liftPeer (g : V → G) (Δ' : DepRel N' V') : PeerRel N V :=
  Δ'.biUnion (fun e => (tryInvPeer g e).toFinset)

end PackageCalculus.PeerDep
