import PackageCalculus.Extensions.Concurrent.Definition
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union

/-! # Concurrent extension: reduction

Encodes a concurrent dependency problem as a core resolution problem by
introducing intermediate packages that mediate version selection between
co-installed siblings. -/

namespace PackageCalculus.Concurrent

variable {N : Type*} {V : Type*} {G : Type*}

inductive ConcurrentName (N V G : Type*) where
  | granular : N → G → ConcurrentName N V G
  | intermediate : N → V → N → ConcurrentName N V G
  deriving DecidableEq

inductive ConcurrentVersion (V G : Type*) where
  | orig : V → ConcurrentVersion V G
  | gran : G → ConcurrentVersion V G
  deriving DecidableEq

variable {N' : Type*} {V' : Type*}
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']

def embedPkg (g : V → G) (p : Package N V) : Package N' V' :=
  (hcnm.granularN p.1 (g p.2), hcvr.origV p.2)

/-- A version set is split when it contains versions of different granularity. -/
def isSplit (g : V → G) (vs : Finset V) : Prop :=
  ∃ u₁ u₂, u₁ ∈ vs ∧ u₂ ∈ vs ∧ g u₁ ≠ g u₂

/-- A version set is direct when all versions have the same granularity. -/
def isDirect (g : V → G) (vs : Finset V) : Prop :=
  ∀ u₁ u₂, u₁ ∈ vs → u₂ ∈ vs → g u₁ = g u₂

variable [DecidableEq N] [DecidableEq V] [DecidableEq G] [DecidableEq N'] [DecidableEq V']

instance decidableIsSplit (g : V → G) (vs : Finset V) : Decidable (isSplit g vs) :=
  decidable_of_iff (∃ u₁ ∈ vs, ∃ u₂ ∈ vs, g u₁ ≠ g u₂)
    ⟨fun ⟨u₁, h₁, u₂, h₂, hne⟩ => ⟨u₁, u₂, h₁, h₂, hne⟩,
     fun ⟨u₁, u₂, h₁, h₂, hne⟩ => ⟨u₁, h₁, u₂, h₂, hne⟩⟩

instance decidableIsDirect (g : V → G) (vs : Finset V) : Decidable (isDirect g vs) :=
  decidable_of_iff (∀ u₁ ∈ vs, ∀ u₂ ∈ vs, g u₁ = g u₂)
    ⟨fun h u₁ u₂ h₁ h₂ => h u₁ h₁ u₂ h₂,
     fun h u₁ h₁ u₂ h₂ => h u₁ u₂ h₁ h₂⟩

def embedReal (R : Real N V) (g : V → G) : Real N' V' :=
  R.image (embedPkg g)

def concurrentReal (R_C : Real N V) (Δ : DepRel N V) (g : V → G) :
    Real N' V' :=
  -- Granular packages: (⟨n, g(v)⟩, orig v)
  embedReal R_C g ∪
  -- Intermediate packages (for the split case): (⟨n, v, m⟩, gran (g u)) for u ∈ vs
  (Δ.biUnion (fun ⟨⟨n, v⟩, m, vs⟩ =>
    if isSplit g vs then
      vs.image (fun u => (hcnm.intermediateN n v m, hcvr.granV (g u)))
    else ∅))

def concurrentDeps (Δ_C : DepRel N V) (g : V → G) :
    DepRel N' V' :=
  -- Direct case: single granular version
  (Δ_C.biUnion (fun ⟨⟨n, v⟩, m, vs⟩ =>
    if isDirect g vs then
      vs.image (fun u =>
        ((hcnm.granularN n (g v), hcvr.origV v),
         hcnm.granularN m (g u),
         vs.map hcvr.origV))
    else ∅)) ∪
  -- Split case: depender to intermediate
  (Δ_C.biUnion (fun ⟨⟨n, v⟩, m, vs⟩ =>
    if isSplit g vs then
      {((hcnm.granularN n (g v), hcvr.origV v),
        hcnm.intermediateN n v m,
        (vs.image (fun u => g u)).map hcvr.granV)}
    else ∅)) ∪
  -- Split case: intermediate to dependee
  (Δ_C.biUnion (fun ⟨⟨n, v⟩, m, vs⟩ =>
    if isSplit g vs then
      vs.image (fun u =>
        ((hcnm.intermediateN n v m, hcvr.granV (g u)),
         hcnm.granularN m (g u),
         (vs.filter (fun w => g w = g u)).map hcvr.origV))
    else ∅)) ∪
  -- Empty case: an unsatisfiable dependency reduces to an unsatisfiable dependency
  (Δ_C.biUnion (fun ⟨⟨n, v⟩, m, vs⟩ =>
    if vs = ∅ then
      {((hcnm.granularN n (g v), hcvr.origV v),
        hcnm.intermediateN n v m,
        (∅ : Finset V'))}
    else ∅))

end PackageCalculus.Concurrent

namespace PackageCalculus

open Function

variable {N V G : Type*}

instance : Concurrent.HasConcurrentNames N V G (Concurrent.ConcurrentName N V G) where
  granularN := Concurrent.ConcurrentName.granular
  granularN_injective := by
    intro a₁ a₂ b₁ b₂ h
    exact ⟨Concurrent.ConcurrentName.granular.inj h |>.1,
           Concurrent.ConcurrentName.granular.inj h |>.2⟩
  intermediateN := Concurrent.ConcurrentName.intermediate
  intermediateN_injective := by
    intro n₁ v₁ m₁ n₂ v₂ m₂ h
    have := Concurrent.ConcurrentName.intermediate.inj h
    exact ⟨this.1, this.2.1, this.2.2⟩
  granularN_ne_intermediateN := fun _ _ _ _ _ => nofun
  intermediateN_ne_granularN := fun _ _ _ _ _ => nofun
  tryGranularN := fun
    | .granular n g => some (n, g)
    | _ => none
  tryGranularN_granularN := fun _ _ => rfl
  tryGranularN_some := fun n' p h => by
    cases n' with
    | granular n g => simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
    | intermediate _ _ _ => simp at h
  tryIntermediateN := fun
    | .intermediate n v m => some (n, v, m)
    | _ => none
  tryIntermediateN_intermediateN := fun _ _ _ => rfl
  tryIntermediateN_some := fun n' p h => by
    cases n' with
    | intermediate n v m => simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; rfl
    | granular _ _ => simp at h

instance : Concurrent.HasConcurrentVersions V G (Concurrent.ConcurrentVersion V G) where
  origV := ⟨Concurrent.ConcurrentVersion.orig,
    fun _ _ h => Concurrent.ConcurrentVersion.orig.inj h⟩
  granV := ⟨Concurrent.ConcurrentVersion.gran,
    fun _ _ h => Concurrent.ConcurrentVersion.gran.inj h⟩
  origV_ne_granV := fun _ _ => nofun
  granV_ne_origV := fun _ _ => nofun
  tryOrigV := fun
    | .orig v => some v
    | _ => none
  tryOrigV_origV := fun _ => rfl
  tryOrigV_some := fun v' v h => by
    cases v' with
    | orig w => simp at h; subst h; rfl
    | gran _ => simp at h

end PackageCalculus
