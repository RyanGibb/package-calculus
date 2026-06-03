import PackageCalculus.Extensions.Virtual.Definition
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union

/-! # Virtual extension: reduction

Encodes virtual packages by routing every dependency on a virtual name through
a synthetic *selector* that picks a concrete provider. -/

namespace PackageCalculus.Virtual

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]

inductive VirtualName (N V : Type*) where
  | orig : N → VirtualName N V
  | selector : Package N V → N → VirtualName N V
  deriving DecidableEq

inductive VirtualVersion (N V : Type*) where
  | orig : V → VirtualVersion N V
  | provider : N → V → VirtualVersion N V
  deriving DecidableEq

variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVirtualNames N V N'] [hvv : HasVirtualVersions N V V']

def embedPkg (p : Package N V) : Package N' V' :=
  (hvn.origN p.1, hvv.origV p.2)

def embedSet (S : Finset (Package N V)) : Finset (Package N' V') :=
  S.image embedPkg

instance decidableMemTop (v : VTop V) (vs : Finset V) : Decidable (memTop v vs) :=
  match v with
  | .top => Decidable.isTrue trivial
  | .val v' => Finset.decidableMem v' vs

def hasProvider (prov : ProvidesRel N V) (n : N) (vs : Finset V) : Prop :=
  ∃ q v, (q, n, v) ∈ prov ∧ memTop v vs

instance decidableHasProvider (prov : ProvidesRel N V) (n : N) (vs : Finset V) :
    Decidable (hasProvider prov n vs) :=
  if h : ∃ x ∈ prov, (x : Package N V × N × VTop V).2.1 = n ∧ memTop x.2.2 vs
  then Decidable.isTrue (by
    obtain ⟨⟨q, n', v⟩, hx, rfl, hv⟩ := h
    exact ⟨q, v, hx, hv⟩)
  else Decidable.isFalse (by
    intro ⟨q, v, hqv, hm⟩
    exact h ⟨(q, n, v), hqv, rfl, hm⟩)

def virtualReal (R_v : Real N V) (Delta : DepRel N V)
    (prov : ProvidesRel N V) :
    Real N' V' :=
  embedSet R_v ∪
  (Delta.biUnion (fun ⟨p, n, vs⟩ =>
    prov.biUnion (fun ⟨⟨m, w⟩, n', v⟩ =>
      if n' = n ∧ memTop v vs then {(hvn.selectorN p n, hvv.providerV m w)} else ∅))) ∪
  (Delta.biUnion (fun ⟨p, n, vs⟩ =>
    if hasProvider prov n vs then
      (vs.filter (fun u => (n, u) ∈ R_v)).image (fun u => (hvn.selectorN p n, hvv.providerV n u))
    else ∅))

def selectorVersions (R_v : Real N V)
    (prov : ProvidesRel N V) (n : N) (vs : Finset V) :
    Finset V' :=
  (prov.biUnion (fun ⟨⟨m, u⟩, n', v⟩ =>
    if n' = n ∧ memTop v vs then {hvv.providerV m u} else ∅)) ∪
  ((vs.filter (fun u => (n, u) ∈ R_v)).image (fun u => hvv.providerV n u))

def virtualDeps (Delta_v : DepRel N V) (R_v : Real N V)
    (prov : ProvidesRel N V) :
    DepRel N' V' :=
  -- No-provider case
  ((Delta_v.filter (fun ⟨_, n, vs⟩ => ¬hasProvider prov n vs)).image
    (fun ⟨p, n, vs⟩ => (embedPkg p, hvn.origN n, vs.map hvv.origV))) ∪
  -- With-provider case: p to selector
  ((Delta_v.filter (fun ⟨_, n, vs⟩ => hasProvider prov n vs)).image
    (fun ⟨p, n, vs⟩ => (embedPkg p, hvn.selectorN p n, selectorVersions R_v prov n vs))) ∪
  -- Selector to provider
  (Delta_v.biUnion (fun ⟨p, n, vs⟩ =>
    prov.biUnion (fun ⟨⟨m, w⟩, n', v⟩ =>
      if n' = n ∧ memTop v vs then
        {((hvn.selectorN p n, hvv.providerV m w), hvn.origN m, {hvv.origV w})}
      else ∅))) ∪
  -- Selector to direct
  (Delta_v.biUnion (fun ⟨p, n, vs⟩ =>
    if hasProvider prov n vs then
      (vs.filter (fun u => (n, u) ∈ R_v)).image
        (fun u => ((hvn.selectorN p n, hvv.providerV n u), hvn.origN n, {hvv.origV u}))
    else ∅))

end PackageCalculus.Virtual

namespace PackageCalculus

open Function

variable {N V : Type*}

instance : Virtual.HasVirtualNames N V (Virtual.VirtualName N V) where
  origN := ⟨Virtual.VirtualName.orig, fun _ _ h => Virtual.VirtualName.orig.inj h⟩
  selectorN := Virtual.VirtualName.selector
  selectorN_injective := by
    intro a₁ a₂ b₁ b₂ h
    exact ⟨Virtual.VirtualName.selector.inj h |>.1,
           Virtual.VirtualName.selector.inj h |>.2⟩
  origN_ne_selectorN := fun _ _ _ => nofun
  selectorN_ne_origN := fun _ _ _ => nofun
  tryOrigN := fun
    | .orig n => some n
    | _ => none
  tryOrigN_origN := fun _ => rfl
  tryOrigN_some := fun n' n h => by
    cases n' with
    | orig m => simp at h; subst h; rfl
    | selector _ _ => simp at h

instance : Virtual.HasVirtualVersions N V (Virtual.VirtualVersion N V) where
  origV := ⟨Virtual.VirtualVersion.orig, fun _ _ h => Virtual.VirtualVersion.orig.inj h⟩
  providerV := Virtual.VirtualVersion.provider
  providerV_injective := by
    intro a₁ a₂ b₁ b₂ h
    exact ⟨Virtual.VirtualVersion.provider.inj h |>.1,
           Virtual.VirtualVersion.provider.inj h |>.2⟩
  origV_ne_providerV := fun _ _ _ => nofun
  providerV_ne_origV := fun _ _ _ => nofun
  tryOrigV := fun
    | .orig v => some v
    | _ => none
  tryOrigV_origV := fun _ => rfl
  tryOrigV_some := fun v' v h => by
    cases v' with
    | orig w => simp at h; subst h; rfl
    | provider _ _ => simp at h

end PackageCalculus
