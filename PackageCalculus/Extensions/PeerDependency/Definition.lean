import PackageCalculus.Extensions.Concurrent.Definition

/-! # Peer-dependency extension: definitions

A `PeerRel` lets a parent constrain which version of a peer name its children
may use. Builds on the concurrent extension via `IsPeerResolution`. -/

namespace PackageCalculus.PeerDep

variable {N : Type*} [DecidableEq N] {V : Type*} [DecidableEq V] {G : Type*}

/-- p Θ (n, vs) means a parent of p can only depend on peer n with a version in vs. -/
abbrev PeerRel (N V : Type*) [DecidableEq N] [DecidableEq V] :=
  Finset (Package N V × N × Finset V)

structure IsPeerResolution
    (R : Real N V) (Δ : DepRel N V)
    (Θ : PeerRel N V) (g : V → G) (r : Package N V)
    (S : Finset (Package N V)) (π : Finset (Package N V × Package N V)) : Prop where
  concurrent : Concurrent.IsConcurrentResolution R Δ g r S π
  /-- If p has peer dep on n, and p's parent q depends on n, the version selected by q via π
      must be in the peer constraint. -/
  peer_satisfaction : ∀ p ∈ S, ∀ n : N, ∀ vs : Finset V,
    (p, n, vs) ∈ Θ →
    ∀ q, (p, q) ∈ π → ∀ us : Finset V, (q, n, us) ∈ Δ →
    ∀ v, v ∈ us → (n, v) ∈ S → ((n, v), q) ∈ π → v ∈ vs

end PackageCalculus.PeerDep
