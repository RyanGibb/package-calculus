import PackageCalculus.Extensions.PeerDependency.Definition
import PackageCalculus.Extensions.Concurrent.Reduction.Definition

/-! # Peer-dependency extension: reduction

Encodes peer constraints by chaining concurrent intermediates with extra
dependencies that propagate the parent's version choice. -/

namespace PackageCalculus.PeerDep

open PackageCalculus.Concurrent PackageCalculus

variable {N : Type*} {V : Type*} {G : Type*}
variable {N' : Type*} {V' : Type*}
variable [hcnm : HasConcurrentNames N V G N'] [hcvr : HasConcurrentVersions V G V']
variable [DecidableEq N] [DecidableEq V] [DecidableEq G] [DecidableEq N'] [DecidableEq V']

def peerReal (R_C : Real N V) (Delta : DepRel N V)
    (Theta : PeerRel N V) (g : V → G) :
    Real N' V' :=
  -- Granular packages
  embedReal R_C g ∪
  -- Intermediate packages: one version per dependee version
  (Delta.biUnion (fun ⟨⟨n, v⟩, m, vs⟩ =>
    vs.image (fun u => (hcnm.intermediateN n v m, hcvr.origV u)))) ∪
  -- Peer intermediate: versions from peer constraint
  (Delta.biUnion (fun ⟨⟨n, v⟩, o, us⟩ =>
    us.biUnion (fun u =>
      (Theta.filter (fun ⟨p, _, _⟩ => p = (o, u))).biUnion (fun ⟨_, m, ws⟩ =>
        ws.image (fun w => (hcnm.intermediateN n v m, hcvr.origV w))))))

def peerDeps (Delta_C : DepRel N V) (Theta : PeerRel N V) (g : V → G) :
    DepRel N' V' :=
  -- Depender to intermediate
  (Delta_C.image (fun ⟨⟨n, v⟩, m, vs⟩ =>
    ((hcnm.granularN n (g v), hcvr.origV v),
     hcnm.intermediateN n v m,
     vs.map hcvr.origV))) ∪
  -- Intermediate to dependee
  (Delta_C.biUnion (fun ⟨⟨n, v⟩, m, vs⟩ =>
    vs.image (fun u =>
      ((hcnm.intermediateN n v m, hcvr.origV u),
       hcnm.granularN m (g u),
       {hcvr.origV u})))) ∪
  -- Peer dep through intermediate (only when parent has dep on peer target)
  (Delta_C.biUnion (fun ⟨⟨n, v⟩, o, us⟩ =>
    us.biUnion (fun u =>
      (Theta.filter (fun ⟨p, _, _⟩ => p = (o, u))).biUnion (fun ⟨_, m, ws⟩ =>
        if Delta_C.filter (fun ⟨p, m', _⟩ => p = (n, v) ∧ m' = m) |>.Nonempty then
          {((hcnm.intermediateN n v o, hcvr.origV u),
            hcnm.intermediateN n v m,
            ws.map hcvr.origV)}
        else ∅))))

end PackageCalculus.PeerDep
