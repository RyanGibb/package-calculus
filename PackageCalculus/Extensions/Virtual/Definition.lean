import PackageCalculus.Core.Definition
import Mathlib.Logic.Embedding.Basic

/-! # Virtual extension: definitions

Virtual packages selecting concrete providers, encoded through a `provides`
relation and the `IsVirtualResolution` structure. -/

namespace PackageCalculus.Virtual

open Function

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V]

/-- A version or top (wildcard). -/
inductive VTop (V : Type*) where
  | val : V → VTop V
  | top : VTop V
  deriving DecidableEq

/-- Provides relation: (provider-package, virtual-name, version-or-top). -/
abbrev ProvidesRel (N V : Type*) [DecidableEq N] [DecidableEq V] :=
  Finset (Package N V × N × VTop V)

/-- v matches vs; top matches anything. -/
def memTop (v : VTop V) (vs : Finset V) : Prop :=
  match v with
  | .top => True
  | .val v' => v' ∈ vs

instance decidableMemTop (v : VTop V) (vs : Finset V) : Decidable (memTop v vs) :=
  match v with
  | .top => Decidable.isTrue trivial
  | .val v' => Finset.decidableMem v' vs

structure IsVirtualResolution
    (R : Real N V) (Delta : DepRel N V)
    (prov : ProvidesRel N V) (r : Package N V)
    (S : Finset (Package N V))
    (rho : Finset (Package N V × N × Package N V)) : Prop where
  subset : S ⊆ R
  root_mem : r ∈ S
  /-- Either a direct version is selected, or exactly one provider satisfies the dep via rho. -/
  virtual_dep_closure : ∀ p ∈ S, ∀ n : N, ∀ vs : Finset V,
    (p, n, vs) ∈ Delta →
    (∃ v ∈ vs, (n, v) ∈ S) ∨
    (∃! q, q ∈ S ∧ ∃ v, memTop v vs ∧ (q, n, v) ∈ prov ∧ (q, n, p) ∈ rho)
  version_unique : VersionUnique S
  /-- rho ⊆ S × N × S: every provider edge relates members of the resolution. -/
  provider_subset : ∀ q : Package N V, ∀ n : N, ∀ p : Package N V,
    (q, n, p) ∈ rho → q ∈ S ∧ p ∈ S

class HasVirtualNames (N V : Type*) (N' : outParam Type*) where
  origN : N ↪ N'
  /-- Synthetic selector name for a (package, dep-name) pair. -/
  selectorN : Package N V → N → N'
  selectorN_injective : Injective2 selectorN
  origN_ne_selectorN : ∀ n p m, origN n ≠ selectorN p m
  selectorN_ne_origN : ∀ p m n, selectorN p m ≠ origN n
  /-- Decidable partial inverse of `origN`. -/
  tryOrigN : N' → Option N
  tryOrigN_origN : ∀ n, tryOrigN (origN n) = some n
  tryOrigN_some : ∀ n' n, tryOrigN n' = some n → origN n = n'
  /-- Decidable partial inverse of `selectorN`. -/
  trySelectorN : N' → Option (Package N V × N)
  trySelectorN_selectorN : ∀ p n, trySelectorN (selectorN p n) = some (p, n)
  trySelectorN_some : ∀ n' q, trySelectorN n' = some q → selectorN q.1 q.2 = n'

attribute [simp] HasVirtualNames.origN_ne_selectorN HasVirtualNames.selectorN_ne_origN

class HasVirtualVersions (N V : Type*) (V' : outParam Type*) where
  origV : V ↪ V'
  /-- Synthetic provider version indexed by (name, version). -/
  providerV : N → V → V'
  providerV_injective : Injective2 providerV
  origV_ne_providerV : ∀ v n w, origV v ≠ providerV n w
  providerV_ne_origV : ∀ n w v, providerV n w ≠ origV v
  /-- Decidable partial inverse of `origV`. -/
  tryOrigV : V' → Option V
  tryOrigV_origV : ∀ v, tryOrigV (origV v) = some v
  tryOrigV_some : ∀ v' v, tryOrigV v' = some v → origV v = v'
  /-- Decidable partial inverse of `providerV`. -/
  tryProviderV : V' → Option (N × V)
  tryProviderV_providerV : ∀ n w, tryProviderV (providerV n w) = some (n, w)
  tryProviderV_some : ∀ v' q, tryProviderV v' = some q → providerV q.1 q.2 = v'

attribute [simp] HasVirtualVersions.origV_ne_providerV HasVirtualVersions.providerV_ne_origV

/-- **No self-provides.** No package provides its own name: provided names are
properly virtual. The reduction routes a dependency on a virtual name through
selector packages whose versions mirror the chosen provider; a self-provider
`⟨⟨n,w⟩, n, v⟩` would make its selector→provider edge structurally identical to
the selector→direct edge for the real version `w` of `n`, so the direct version
set could not be separated from the providers in the reduced problem. This is
the condition under which the dependency relation is recoverable up to
`restrictReal` (transpiling retraction). -/
def ProvidesRel.NoSelfProvides (prov : ProvidesRel N V) : Prop :=
  ∀ q n v, (q, n, v) ∈ prov → q.1 ≠ n

/-- The instantiation of a provides relation on a dependency relation: the
admissible (provider, name, depender) triples, mirroring the shape of ρ.
Guards are consulted only against the version sets Δ actually contains, so
this is the normal form of `prov` that resolution semantics observes
(`instantiate_resolution_congr`). -/
def ProvidesRel.instantiate (prov : ProvidesRel N V) (Δ : DepRel N V) :
    Finset (Package N V × N × Package N V) :=
  Δ.biUnion fun e => prov.biUnion fun t =>
    if t.2.1 = e.2.1 ∧ memTop t.2.2 e.2.2 then {(t.1, e.2.1, e.1)} else ∅

theorem ProvidesRel.mem_instantiate {prov : ProvidesRel N V} {Δ : DepRel N V}
    {q p : Package N V} {n : N} :
    (q, n, p) ∈ prov.instantiate Δ ↔
      ∃ vs, (p, n, vs) ∈ Δ ∧ ∃ v, memTop v vs ∧ (q, n, v) ∈ prov := by
  simp only [ProvidesRel.instantiate, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨p₁, n₁, vs⟩, hdep, ⟨q₁, n₂, v⟩, hprov, hif⟩
    split at hif
    · rename_i hc
      simp only at hc
      obtain ⟨hn, hm⟩ := hc
      rw [Finset.mem_singleton] at hif
      obtain ⟨rfl, rfl, rfl⟩ := hif
      subst hn
      exact ⟨vs, hdep, v, hm, hprov⟩
    · exact absurd hif (Finset.notMem_empty _)
  · rintro ⟨vs, hdep, v, hv, hprov⟩
    refine ⟨(p, n, vs), hdep, (q, n, v), hprov, ?_⟩
    rw [if_pos ⟨rfl, hv⟩]
    exact Finset.mem_singleton_self _

/-- Resolutions consult the provides relation only through its instantiation:
provides relations with the same instantiation on Δ admit the same
resolutions. -/
theorem instantiate_resolution_congr {R : Real N V} {Δ : DepRel N V}
    {prov prov' : ProvidesRel N V} {r : Package N V}
    {S : Finset (Package N V)}
    {rho : Finset (Package N V × N × Package N V)}
    (hfn : Δ.FunctionalInName)
    (h : prov.instantiate Δ = prov'.instantiate Δ) :
    IsVirtualResolution R Δ prov r S rho ↔ IsVirtualResolution R Δ prov' r S rho := by
  suffices aux : ∀ {P P' : ProvidesRel N V}, P.instantiate Δ = P'.instantiate Δ →
      IsVirtualResolution R Δ P r S rho → IsVirtualResolution R Δ P' r S rho from
    ⟨aux h, aux h.symm⟩
  intro P P' h hres
  refine ⟨hres.subset, hres.root_mem, ?_, hres.version_unique, hres.provider_subset⟩
  intro p hp n vs hdep
  rcases hres.virtual_dep_closure p hp n vs hdep with
    hdir | ⟨q, ⟨hqS, v, hv, hP, hrho⟩, huniq⟩
  · exact Or.inl hdir
  · have hq : (q, n, p) ∈ P'.instantiate Δ := by
      rw [← h]
      exact ProvidesRel.mem_instantiate.mpr ⟨vs, hdep, v, hv, hP⟩
    obtain ⟨vs', hdep', v', hv', hP'⟩ := ProvidesRel.mem_instantiate.mp hq
    obtain rfl := hfn p n vs vs' hdep hdep'
    refine Or.inr ⟨q, ⟨hqS, v', hv', hP', hrho⟩, ?_⟩
    rintro q₂ ⟨hq₂S, v₂, hv₂, hP₂, hrho₂⟩
    apply huniq q₂
    have hq₂ : (q₂, n, p) ∈ P.instantiate Δ := by
      rw [h]
      exact ProvidesRel.mem_instantiate.mpr ⟨vs, hdep, v₂, hv₂, hP₂⟩
    obtain ⟨vs₂, hdep₂, v₀, hv₀, hP₀⟩ := ProvidesRel.mem_instantiate.mp hq₂
    obtain rfl := hfn p n vs vs₂ hdep hdep₂
    exact ⟨hq₂S, v₀, hv₀, hP₀, hrho₂⟩

end PackageCalculus.Virtual
