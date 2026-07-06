import PackageCalculus.Extensions.VariableFormula.Definition
import PackageCalculus.Extensions.Conflict.Reduction.Definition

/-! # Variable-formula extension: reduction

Encodes formulae with package and version variables into the core calculus by
materialising a candidate witness per literal and routing dependencies through
synthetic names. -/

namespace PackageCalculus.VarFormula

variable {N : Type*} {V : Type*} {X : Type*} {Y : Type*}

/-- Concrete name carrier for the Variable Formula calculus. Single
`var x` constructor (no global/local split). -/
inductive VFName (N V X Y : Type*) where
  | orig : N → VFName N V X Y
  | var : X → VFName N V X Y
  | disjunct : Formula N V X Y → Formula N V X Y → VFName N V X Y
  | negDep : N → Finset V → VFName N V X Y

inductive VFVersion (V Y : Type*) where
  | orig : V → VFVersion V Y
  | zero : VFVersion V Y
  | one : VFVersion V Y
  | varVal : Y → VFVersion V Y

variable {N' : Type*} [DecidableEq N'] {V' : Type*} [DecidableEq V']
variable [hvn : HasVFNames N V X Y N'] [hvv : HasVFVersions V Y V']

def embedPkg (p : Package N V) : Package N' V' :=
  (hvn.origN p.1, hvv.origV p.2)

/-- The logical complement of a comparison operator. -/
def CmpOp.complement : PackageCalculus.CmpOp → PackageCalculus.CmpOp
  | .ge => .lt
  | .gt => .le
  | .le => .gt
  | .lt => .ge
  | .eq => .ne
  | .ne => .eq

def Formula.weight : Formula N V X Y → Nat
  | .dep _ _ => 0
  | .conj ψ₁ ψ₂ => ψ₁.weight + ψ₂.weight + 2
  | .disj ψ₁ ψ₂ => ψ₁.weight + ψ₂.weight + 2
  | .neg ψ => 3 * (ψ.weight + 1)
  | .varCmp _ _ _ => 0

/-! ### NNF atoms

As for package formulae, the encoding erases conjunction structure and drives
negations inward; additionally, a variable comparison `x ω y` survives only as
its *extension* — the set of domain values satisfying it — since the edge
carries the evaluated version set and negated comparisons fold into complement
operators. The preserved normal form is therefore the set of NNF atoms with
variable atoms normalised to their extension over the declared domain. -/

/-- An NNF atom: a positive literal, a negative literal, a disjunction kept
whole, or a variable constrained to a set of domain values (the *extension*
of a comparison over the declared domain). -/
inductive Atom (N V X Y : Type*) where
  | pos : N → Finset V → Atom N V X Y
  | neg : N → Finset V → Atom N V X Y
  | disj : Formula N V X Y → Formula N V X Y → Atom N V X Y
  | var : X → Finset Y → Atom N V X Y
  deriving DecidableEq

/-- Satisfaction of an atom by a resolution set and an assignment. -/
def Atom.satisfies [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
    [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (S : Finset (Package N V)) (σ : X → Y) : Atom N V X Y → Prop
  | .pos n vs => ∃ v ∈ vs, (n, v) ∈ S
  | .neg n vs => ¬∃ v ∈ vs, (n, v) ∈ S
  | .disj ψ₁ ψ₂ => ψ₁.satisfies S σ ∨ ψ₂.satisfies S σ
  | .var x ys => σ x ∈ ys

variable [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y] in
/-- The NNF atoms of a formula over the per-variable domain `Y_x`, mirroring
the recursion of `encodeNNF`. -/
def atoms [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (Y_x : X → Finset Y) : Formula N V X Y → Finset (Atom N V X Y)
  | .dep n vs => {.pos n vs}
  | .conj ψ_L ψ_R => atoms Y_x ψ_L ∪ atoms Y_x ψ_R
  | .disj ψ_L ψ_R => {.disj ψ_L ψ_R}
  | .varCmp x ω y => {.var x ((Y_x x).filter (fun y' => ω.eval y' y))}
  | .neg (.dep n vs) => {.neg n vs}
  | .neg (.varCmp x ω y) =>
    {.var x ((Y_x x).filter (fun y' => (CmpOp.complement ω).eval y' y))}
  | .neg (.conj ψ_L ψ_R) => {.disj (.neg ψ_L) (.neg ψ_R)}
  | .neg (.disj ψ_L ψ_R) => atoms Y_x (.neg ψ_L) ∪ atoms Y_x (.neg ψ_R)
  | .neg (.neg ψ) => atoms Y_x ψ
termination_by ψ => ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

instance cmpOp_eval_decidable [inst_lt : LT Y] [DecidableEq Y]
    [DecidableRel (inst_lt.lt : Y → Y → Prop)]
    (ω : PackageCalculus.CmpOp) (y : Y) : DecidablePred (fun y' => ω.eval y' y = true) := by
  intro y'
  exact inferInstance

/-- Restrict the variable-domain `Y_x` of values satisfying `ω_y y` and embed
into `V'`. The domain `Y_x` is supplied as an argument. -/
def cmpVersionSet [LT Y] [DecidableEq Y] [DecidableRel (· < · : Y → Y → Prop)]
    (Y_x : Finset Y) (ω : PackageCalculus.CmpOp) (y : Y) : Finset V' :=
  (Y_x.filter (fun y' => ω.eval y' y)).map hvv.varValV

/-- Encoding function `E`, single depender argument (no `p₀` threading).

Takes the per-variable domain `Y_x : X → Finset Y`. -/
def encodeNNF [LT Y] [DecidableEq Y] [DecidableRel (· < · : Y → Y → Prop)]
    (Y_x : X → Finset Y)
    (p : Package N' V') :
    (ψ : Formula N V X Y) →
    Finset (Package N' V' × N' × Finset V')
  | .dep n vs =>
    { (p, hvn.origN n, vs.map hvv.origV) }
  | .conj ψ_L ψ_R =>
    encodeNNF Y_x p ψ_L ∪ encodeNNF Y_x p ψ_R
  | .disj ψ_L ψ_R =>
    { (p, hvn.disjunctN ψ_L ψ_R, {hvv.zeroV, hvv.oneV}) } ∪
    encodeNNF Y_x (hvn.disjunctN ψ_L ψ_R, hvv.zeroV) ψ_L ∪
    encodeNNF Y_x (hvn.disjunctN ψ_L ψ_R, hvv.oneV) ψ_R
  | .varCmp x ω y =>
    { (p, hvn.varN x, cmpVersionSet (hvv := hvv) (Y_x x) ω y) }
  | .neg (.dep n vs) =>
    { (p, hvn.syntheticN n vs, ({hvv.oneV} : Finset V')) } ∪
    vs.image (fun u => ((hvn.origN n, hvv.origV u),
      hvn.syntheticN n vs, ({hvv.zeroV} : Finset V')))
  | .neg (.varCmp x ω y) =>
    encodeNNF Y_x p (.varCmp x (VarFormula.CmpOp.complement ω) y)
  | .neg (.conj ψ_L ψ_R) =>
    encodeNNF Y_x p (.disj (.neg ψ_L) (.neg ψ_R))
  | .neg (.disj ψ_L ψ_R) =>
    encodeNNF Y_x p (.conj (.neg ψ_L) (.neg ψ_R))
  | .neg (.neg ψ) =>
    encodeNNF Y_x p ψ
termination_by ψ => ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

def encode [LT Y] [DecidableEq Y] [DecidableRel (· < · : Y → Y → Prop)]
    (Y_x : X → Finset Y)
    (p : Package N' V')
    (ψ : Formula N V X Y) :
    Finset (Package N' V' × N' × Finset V') :=
  encodeNNF Y_x p ψ

/-- Collect all witness packages generated by encoding a formula. -/
def witnessPackages [LT Y] [DecidableEq Y] [DecidableRel (· < · : Y → Y → Prop)]
    (p : Package N' V') :
    (ψ : Formula N V X Y) → Finset (Package N' V')
  | .dep _ _ => ∅
  | .conj ψ_L ψ_R =>
    witnessPackages p ψ_L ∪ witnessPackages p ψ_R
  | .disj ψ_L ψ_R =>
    {(hvn.disjunctN ψ_L ψ_R, hvv.zeroV), (hvn.disjunctN ψ_L ψ_R, hvv.oneV)} ∪
    witnessPackages (hvn.disjunctN ψ_L ψ_R, hvv.zeroV) ψ_L ∪
    witnessPackages (hvn.disjunctN ψ_L ψ_R, hvv.oneV) ψ_R
  | .varCmp _ _ _ => ∅
  | .neg (.dep n vs) =>
    {(hvn.syntheticN n vs, hvv.zeroV), (hvn.syntheticN n vs, hvv.oneV)}
  | .neg (.varCmp x ω y) =>
    witnessPackages p (.varCmp x (VarFormula.CmpOp.complement ω) y)
  | .neg (.conj ψ_L ψ_R) =>
    witnessPackages p (.disj (.neg ψ_L) (.neg ψ_R))
  | .neg (.disj ψ_L ψ_R) =>
    witnessPackages p (.conj (.neg ψ_L) (.neg ψ_R))
  | .neg (.neg ψ) =>
    witnessPackages p ψ
termination_by ψ => ψ.weight
decreasing_by all_goals simp only [Formula.weight]; omega

variable [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y]

/-- Reduced real packages: original packages, formula witnesses, and one
package per (variable, value) pair in `Y_x`. -/
def vfReal [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (Y_x : X → Finset Y) [Fintype X]
    (R_Ψ : Real N V) (Δ_Ψ : VFDepRel N V X Y) :
    Real N' V' :=
  R_Ψ.image (embedPkg (X := X) (Y := Y)) ∪
  Δ_Ψ.biUnion (fun ⟨p, ψ⟩ => witnessPackages (embedPkg (X := X) (Y := Y) p) ψ) ∪
  Finset.univ.biUnion (fun x : X =>
    (Y_x x).image (fun y => ((hvn.varN x, hvv.varValV y) : Package N' V')))

def vfDeps [LT Y] [DecidableRel (· < · : Y → Y → Prop)]
    (Y_x : X → Finset Y)
    (Δ_Ψ : VFDepRel N V X Y) :
    DepRel N' V' :=
  Δ_Ψ.biUnion (fun ⟨p, ψ⟩ => encode Y_x (embedPkg (X := X) (Y := Y) p) ψ)

omit [DecidableEq Y] in
theorem complement_eval [LT Y] [DecidableEq Y] [DecidableRel (· < · : Y → Y → Prop)]
    (ω : PackageCalculus.CmpOp) (x y : Y) :
    ((CmpOp.complement ω).eval x y = true) ↔ ¬(ω.eval x y = true) := by
  cases ω <;> simp [CmpOp.complement, PackageCalculus.CmpOp.eval]

omit [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
  [DecidableEq N'] [DecidableEq V'] in
theorem mem_cmpVersionSet [LT Y] [DecidableEq Y]
    [DecidableRel (· < · : Y → Y → Prop)]
    (Y_x : Finset Y) (ω : PackageCalculus.CmpOp) (y y' : Y) :
    hvv.varValV y' ∈ cmpVersionSet (hvv := hvv) Y_x ω y ↔ y' ∈ Y_x ∧ ω.eval y' y := by
  simp [cmpVersionSet, Finset.mem_filter]

omit [DecidableEq N] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
  [DecidableEq N'] [DecidableEq V'] in
theorem mem_cmpVersionSet' [LT Y] [DecidableEq Y]
    [DecidableRel (· < · : Y → Y → Prop)]
    {Y_x : Finset Y} {ω : PackageCalculus.CmpOp} {y : Y} {w : V'} :
    w ∈ cmpVersionSet (hvv := hvv) Y_x ω y →
      ∃ y', w = hvv.varValV y' ∧ y' ∈ Y_x ∧ ω.eval y' y := by
  intro hw
  unfold cmpVersionSet at hw
  rw [Finset.mem_map] at hw
  obtain ⟨y', hy'mem, rfl⟩ := hw
  rw [Finset.mem_filter] at hy'mem
  exact ⟨y', rfl, hy'mem.1, hy'mem.2⟩

end PackageCalculus.VarFormula

namespace PackageCalculus

open Function

variable {N V X Y : Type*}

instance : VarFormula.HasVFNames N V X Y (VarFormula.VFName N V X Y) where
  toHasConflictNames :=
    { origN := ⟨VarFormula.VFName.orig, fun _ _ h => VarFormula.VFName.orig.inj h⟩
      syntheticN := VarFormula.VFName.negDep
      syntheticN_injective := by
        intro a₁ a₂ b₁ b₂ h
        exact ⟨VarFormula.VFName.negDep.inj h |>.1,
               VarFormula.VFName.negDep.inj h |>.2⟩
      origN_ne_syntheticN := fun _ _ _ => nofun
      syntheticN_ne_origN := fun _ _ _ => nofun
      tryOrigN := fun
        | .orig n => some n
        | _ => none
      tryOrigN_origN := fun _ => rfl
      tryOrigN_some := fun n' n h => by
        cases n' with
        | orig m => simp at h; subst h; rfl
        | _ => simp at h
      trySyntheticN := fun
        | .negDep n vs => some (n, vs)
        | _ => none
      trySyntheticN_syntheticN := fun _ _ => rfl
      trySyntheticN_some := fun n' p h => by
        cases n' with
        | negDep n vs => simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
        | _ => simp at h }
  varN := ⟨VarFormula.VFName.var, fun _ _ h => VarFormula.VFName.var.inj h⟩
  disjunctN := VarFormula.VFName.disjunct
  disjunctN_injective := by
    intro a₁ a₂ b₁ b₂ h
    exact ⟨VarFormula.VFName.disjunct.inj h |>.1,
           VarFormula.VFName.disjunct.inj h |>.2⟩
  origN_ne_varN := fun _ _ => nofun
  varN_ne_origN := fun _ _ => nofun
  origN_ne_disjunctN := fun _ _ _ => nofun
  disjunctN_ne_origN := fun _ _ _ => nofun
  varN_ne_disjunctN := fun _ _ _ => nofun
  disjunctN_ne_varN := fun _ _ _ => nofun
  varN_ne_syntheticN := fun _ _ _ => nofun
  syntheticN_ne_varN := fun _ _ _ => nofun
  disjunctN_ne_syntheticN := fun _ _ _ _ => nofun
  syntheticN_ne_disjunctN := fun _ _ _ _ => nofun
  tryVarN := fun
    | .var x => some x
    | _ => none
  tryVarN_varN := fun _ => rfl
  tryVarN_some := fun n' x h => by
    cases n' with
    | var x₀ => simp at h; subst h; rfl
    | _ => simp at h
  tryDisjunctN := fun
    | .disjunct ψ₁ ψ₂ => some (ψ₁, ψ₂)
    | _ => none
  tryDisjunctN_disjunctN := fun _ _ => rfl
  tryDisjunctN_some := fun n' q h => by
    cases n' with
    | disjunct a b => simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
    | _ => simp at h

instance : VarFormula.HasVFVersions V Y (VarFormula.VFVersion V Y) where
  toHasConflictVersions :=
    { origV := ⟨VarFormula.VFVersion.orig, fun _ _ h => VarFormula.VFVersion.orig.inj h⟩
      zeroV := VarFormula.VFVersion.zero
      oneV := VarFormula.VFVersion.one
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
        | _ => simp at h }
  varValV := ⟨VarFormula.VFVersion.varVal, fun _ _ h => VarFormula.VFVersion.varVal.inj h⟩
  origV_ne_varValV := fun _ _ => nofun
  varValV_ne_origV := fun _ _ => nofun
  zeroV_ne_varValV := fun _ => nofun
  varValV_ne_zeroV := fun _ => nofun
  oneV_ne_varValV := fun _ => nofun
  varValV_ne_oneV := fun _ => nofun
  tryVarValV := fun
    | .varVal y => some y
    | _ => none
  tryVarValV_varValV := fun _ => rfl
  tryVarValV_some := fun v' y h => by
    cases v' with
    | varVal y₀ => simp at h; subst h; rfl
    | _ => simp at h

end PackageCalculus
