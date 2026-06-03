import PackageCalculus.Extensions.Conflict.Definition
import Mathlib.Data.Finset.Union

/-! # Conflict extension: reduction

Encodes a conflict relation as core dependencies using *synthetic* names whose
presence forbids the conflicting versions. -/

namespace PackageCalculus.Conflict

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]

inductive ConflictName (N V : Type*) where
  | orig : N → ConflictName N V
  | synthetic : N → Finset V → ConflictName N V
  deriving DecidableEq

inductive ConflictVersion (V : Type*) where
  | orig : V → ConflictVersion V
  | zero : ConflictVersion V
  | one : ConflictVersion V
  deriving DecidableEq

variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hcn : HasConflictNames N V N'] [hcv : HasConflictVersions V V']

def embedPkg (p : Package N V) : Package N' V' :=
  (hcn.origN p.1, hcv.origV p.2)

def embedSet (S : Finset (Package N V)) : Finset (Package N' V') :=
  S.image embedPkg

def embedVS (vs : Finset V) : Finset V' :=
  vs.map hcv.origV

def conflictReal (R_Γ : Real N V) (Γ : ConflictRel N V) :
    Real N' V' :=
  embedSet R_Γ ∪
  (Γ.biUnion (fun ⟨_, n, vs⟩ =>
    {(hcn.syntheticN n vs, hcv.zeroV), (hcn.syntheticN n vs, hcv.oneV)}))

def conflictDeps (Δ_Γ : DepRel N V) (Γ : ConflictRel N V) :
    DepRel N' V' :=
  -- Original dependencies, embedded
  (Δ_Γ.image (fun ⟨p, m, vs⟩ => (embedPkg p, hcn.origN m, embedVS vs))) ∪
  -- Conflicter p depends on ⟨n, vs⟩ version 1
  (Γ.image (fun ⟨p, n, vs⟩ => (embedPkg p, hcn.syntheticN n vs, {hcv.oneV}))) ∪
  -- Conflictee (n, u) depends on ⟨n, vs⟩ version 0
  (Γ.biUnion (fun ⟨_, n, vs⟩ =>
    vs.image (fun u => ((hcn.origN n, hcv.origV u), hcn.syntheticN n vs, {hcv.zeroV}))))

def conflictReduce (R : Real N V) (Δ : DepRel N V) (Γ : ConflictRel N V) :
    Real N' V' × DepRel N' V' :=
  (conflictReal R Γ, conflictDeps Δ Γ)

end PackageCalculus.Conflict

namespace PackageCalculus

open Function

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]

instance : Conflict.HasConflictNames N V (Conflict.ConflictName N V) where
  origN := ⟨Conflict.ConflictName.orig, fun _ _ h => Conflict.ConflictName.orig.inj h⟩
  syntheticN := Conflict.ConflictName.synthetic
  syntheticN_injective := by
    intro a₁ a₂ b₁ b₂ h
    exact ⟨Conflict.ConflictName.synthetic.inj h |>.1,
           Conflict.ConflictName.synthetic.inj h |>.2⟩
  origN_ne_syntheticN := fun _ _ _ => nofun
  syntheticN_ne_origN := fun _ _ _ => nofun
  tryOrigN := fun
    | .orig n => some n
    | _ => none
  tryOrigN_origN := fun _ => rfl
  tryOrigN_some := fun n' n h => by
    cases n' with
    | orig m => simp at h; subst h; rfl
    | synthetic _ _ => simp at h
  trySyntheticN := fun
    | .synthetic n vs => some (n, vs)
    | _ => none
  trySyntheticN_syntheticN := fun _ _ => rfl
  trySyntheticN_some := fun n' p h => by
    cases n' with
    | orig _ => simp at h
    | synthetic n vs => simp at h; obtain ⟨rfl, rfl⟩ := h; rfl

instance : Conflict.HasConflictVersions V (Conflict.ConflictVersion V) where
  origV := ⟨Conflict.ConflictVersion.orig, fun _ _ h => Conflict.ConflictVersion.orig.inj h⟩
  zeroV := Conflict.ConflictVersion.zero
  oneV := Conflict.ConflictVersion.one
  origV_ne_zeroV := fun _ => nofun
  zeroV_ne_origV := fun _ => nofun
  origV_ne_oneV := fun _ => nofun
  oneV_ne_origV := fun _ => nofun
  zeroV_ne_oneV := nofun
  oneV_ne_zeroV := nofun
  tryOrigV := fun
    | .orig v => some v
    | _ => none
  tryOrigV_origV := fun _ => rfl
  tryOrigV_some := fun v' v h => by
    cases v' with
    | orig w => simp at h; subst h; rfl
    | zero => simp at h
    | one => simp at h

end PackageCalculus
