These tables map each definition and theorem in the paper to its mechanised counterpart in this development.
All file paths are relative to the `PackageCalculus/` source directory.

Where the paper writes structured names like `⟨n, vs⟩ ∈ N` or `⟨n, f⟩`, the Lean uses dedicated inductive name/version types and `Has*Names` / `Has*Versions` typeclasses to inject them.

The paper states one standing condition on every dependency relation: Functional in Name (Def 3.1.2).
In Lean it appears as an explicit hypothesis (`DepRel.FunctionalInName`) on the theorems that consume it.
The paper's normalisation remark -- merging same-name entries per depender by intersecting their version sets -- is mechanised as `DepRel.merge` (`merge_functionalInName`, `merge_resolution_iff`), alongside `DepRel.restrictReal` (`restrictReal_resolution_iff`) for restricting version sets to real packages; both preserve the set of resolutions.

## 3. The Package Calculus

| Paper                                        | Lean                                                   | File                                    |
| -------------------------------------------- | ------------------------------------------------------ | ----------------------------------------|
| Def 3.1.1 Package                            | `Real`, `Package`                                      | `Core/Definition.lean`                  |
| Def 3.1.2 Dependency                         | `DepRel`                                               | `Core/Definition.lean`                  |
| Def 3.1.3 Resolution                         | `IsResolution`                                         | `Core/Definition.lean`                  |
| Thm 3.1.4 `DependencyResolution` NP-complete | see Appendix B below (`satRed_*`)                      | `Complexity/`                           |
| Def 3.2.1 Version Ordering                   | the `[LT V]` / `[DecidableRel (· < ·)]` order on `V`   | used throughout `Versions/Formula.lean` |
| Def 3.2.2 Version Formula                    | `VersionFormula`, `VersionFormula.eval` (`CmpOp.eval`) | `Versions/Formula.lean`                 |
| Def 3.2.3 Version Formula Dependency         | `VFDepRel`                                             | `Versions/Formula.lean`                 |
| Def 3.2.4 Version Formula Resolution         | `IsVFResolution`                                       | `Versions/Formula.lean`                 |
| Def 3.2.5 Version Formula Reduction          | `vfReduce`                                             | `Versions/Reduction/Definition.lean`    |
| Thm 3.2.6 Correctness                        | `version_formula_correct`                              | `Versions/Reduction/Correctness.lean`   |

## 4. Package Managers, Mise en Place

### 4.1 Conflicts

| Paper                         | Lean                            | File                                              |
| ----------------------------- | ------------------------------- | ------------------------------------------------- |
| Def 4.1.1 Conflict            | `ConflictRel`                   | `Extensions/Conflict/Definition.lean`             |
| Def 4.1.2 Conflict Resolution | `IsConflictResolution`          | `Extensions/Conflict/Definition.lean`             |
| Def 4.1.3 Conflict Reduction  | `conflictReal` / `conflictDeps` | `Extensions/Conflict/Reduction/Definition.lean`   |
| Thm 4.1.4 Soundness           | `conflict_soundness`            | `Extensions/Conflict/Reduction/Soundness.lean`    |
| Thm 4.1.5 Completeness        | `conflict_completeness`         | `Extensions/Conflict/Reduction/Completeness.lean` |

### 4.2 Concurrent Versions

| Paper                           | Lean                                | File                                                |
| ------------------------------- | ----------------------------------- | --------------------------------------------------- |
| Def 4.2.1 Granularity Function  | `g : V → G` (parameter)             | `Extensions/Concurrent/Definition.lean`             |
| Def 4.2.2 Concurrent Resolution | `IsConcurrentResolution`            | `Extensions/Concurrent/Definition.lean`             |
| Def 4.2.3 Concurrent Reduction  | `concurrentReal` / `concurrentDeps` | `Extensions/Concurrent/Reduction/Definition.lean`   |
| Thm 4.2.4 Soundness             | `concurrent_soundness`              | `Extensions/Concurrent/Reduction/Soundness.lean`    |
| Thm 4.2.5 Completeness          | `concurrent_completeness`           | `Extensions/Concurrent/Reduction/Completeness.lean` |

### 4.3 Peer Dependencies

| Paper                                | Lean                    | File                                                    |
| ------------------------------------ | ----------------------- | ------------------------------------------------------- |
| Def 4.3.1 Peer Dependency            | `PeerRel`               | `Extensions/PeerDependency/Definition.lean`             |
| Def 4.3.2 Peer Dependency Resolution | `IsPeerResolution`      | `Extensions/PeerDependency/Definition.lean`             |
| Def 4.3.3 Peer Dependency Reduction  | `peerReal` / `peerDeps` | `Extensions/PeerDependency/Reduction/Definition.lean`   |
| Thm 4.3.4 Soundness                  | `peer_soundness`        | `Extensions/PeerDependency/Reduction/Soundness.lean`    |
| Thm 4.3.5 Completeness               | `peer_completeness`     | `Extensions/PeerDependency/Reduction/Completeness.lean` |

### 4.4 Features

| Paper                        | Lean                          | File                                             |
| ---------------------------- | ----------------------------- | ------------------------------------------------ |
| Def 4.4.1 Feature            | `Support`                     | `Extensions/Feature/Definition.lean`             |
| Def 4.4.2 Feature Dependency | `FeatDepRel`, `AddlDepRel`    | `Extensions/Feature/Definition.lean`             |
| Def 4.4.3 Feature Resolution | `IsFeatureResolution`         | `Extensions/Feature/Definition.lean`             |
| Def 4.4.4 Feature Reduction  | `featureReal` / `featureDeps` | `Extensions/Feature/Reduction/Definition.lean`   |
| Thm 4.4.5 Soundness          | `feature_soundness`           | `Extensions/Feature/Reduction/Soundness.lean`    |
| Thm 4.4.6 Completeness       | `feature_completeness`        | `Extensions/Feature/Reduction/Completeness.lean` |

### 4.5 Package Formulae

| Paper                                | Lean                                             | File                                                    |
| ------------------------------------ | ------------------------------------------------ | ------------------------------------------------------- |
| Def 4.5.1 Package Formula            | `Formula` (in namespace `PkgFormula`)            | `Extensions/PackageFormula/Definition.lean`             |
| Def 4.5.2 Package Formula Dependency | `PFDepRel`                                       | `Extensions/PackageFormula/Definition.lean`             |
| Def 4.5.3 Package Formula Resolution | `IsPFResolution`                                 | `Extensions/PackageFormula/Definition.lean`             |
| Def 4.5.4 Package Formula Reduction  | `pfReal` / `pfDeps` (via `encode` / `encodeNNF`) | `Extensions/PackageFormula/Reduction/Definition.lean`   |
| Thm 4.5.5 Soundness                  | `package_formula_soundness`                      | `Extensions/PackageFormula/Reduction/Soundness.lean`    |
| Thm 4.5.6 Completeness               | `package_formula_completeness`                   | `Extensions/PackageFormula/Reduction/Completeness.lean` |

### 4.6 Variable Formulae

| Paper                                 | Lean                                                                    | File                                                     |
| ------------------------------------- | ----------------------------------------------------------------------- | -------------------------------------------------------- |
| Def 4.6.1 Variable Formula            | `Formula N V X Y` (in namespace `VarFormula`), dep. relation `VFDepRel` | `Extensions/VariableFormula/Definition.lean`             |
| Def 4.6.2 Variable Formula Resolution | `IsVFResolution`                                                        | `Extensions/VariableFormula/Definition.lean`             |
| Def 4.6.3 Variable Formula Reduction  | `vfReal` / `vfDeps`                                                     | `Extensions/VariableFormula/Reduction/Definition.lean`   |
| Thm 4.6.4 Soundness                   | `variable_formula_soundness`                                            | `Extensions/VariableFormula/Reduction/Soundness.lean`    |
| Thm 4.6.5 Completeness                | `variable_formula_completeness`                                         | `Extensions/VariableFormula/Reduction/Completeness.lean` |

### 4.7 Virtual Packages

| Paper                                | Lean                          | File                                             |
| ------------------------------------ | ----------------------------- | ------------------------------------------------ |
| Def 4.7.1 Virtual Package Provides   | `ProvidesRel`                 | `Extensions/Virtual/Definition.lean`             |
| Def 4.7.2 Virtual Package Resolution | `IsVirtualResolution`         | `Extensions/Virtual/Definition.lean`             |
| Def 4.7.3 Virtual Package Reduction  | `virtualReal` / `virtualDeps` | `Extensions/Virtual/Reduction/Definition.lean`   |
| Thm 4.7.4 Soundness                  | `virtual_soundness`           | `Extensions/Virtual/Reduction/Soundness.lean`    |
| Thm 4.7.5 Completeness               | `virtual_completeness`        | `Extensions/Virtual/Reduction/Completeness.lean` |

## 5. Package Managers, à la Carte

### 5.1 Composition of Extensions

| Paper                                   | Lean                                              | File                                                        |
| --------------------------------------- | ------------------------------------------------- | ----------------------------------------------------------- |
| Def 5.1.1 Concurrent Feature Resolution | `IsConcurrentFeatureResolution`                   | `Composition/FeatureConcurrent/Definition.lean`             |
| Def 5.1.2 Concurrent Feature Reduction  | `concurrentFeatureReal` / `concurrentFeatureDeps` | `Composition/FeatureConcurrent/Reduction/Definition.lean`   |
| Thm 5.1.3 Soundness                     | `concurrent_feature_soundness`                    | `Composition/FeatureConcurrent/Reduction/Soundness.lean`    |
| Thm 5.1.4 Completeness                  | `concurrent_feature_completeness`                 | `Composition/FeatureConcurrent/Reduction/Completeness.lean` |

### 5.2 Transpiling Packaging Languages

The per-extension lifting of §5.2 is mechanised in each extension's `Lifting/` subdirectory, under `Extensions/<Extension>/Lifting/` and `Versions/Lifting/`: `Lifting/Definition.lean` defines `lift`, `Lifting/Retraction.lean` proves round-trip theorems, and `Lifting/{Soundness,Completeness}.lean` show `lift` carries core resolutions back to extension resolutions.
The full instance-level retraction `lift ∘ reduce = id` is mechanised for four extensions.
For Conflict, `conflictLift_conflictReduce` covers packages, dependencies, and conflicts.
For Concurrent, `concurrentLift_concurrentReduce` covers packages and dependencies, assuming the standing `DepRel.FunctionalInName` normalisation on the source relation (needed because a split entry's version set is only recoverable once same-name entries have been merged); the dependency component `liftDeps_concurrentDeps` reassembles each split entry's version set as the union of the granularity groups carried by the intermediate→dependee edges (`gatherVs`), and recovers direct and empty entries edge-locally. This required adding a partial inverse `tryIntermediateN` for the intermediate-name constructor to `HasConcurrentNames`.
For Peer dependencies, `peerLift_peerReduce` covers packages, dependencies, and the peer relation. Because peer edges carry the whole version set (no granularity split), both `liftDeps_peerDeps` (dependency relation) and `liftPeer_peerDeps` (peer relation) recover their entries edge-locally. The dependency component needs no side-condition; the peer component assumes the peer relation is `PeerRel.GroundedIn` the dependency relation -- every peer constraint is witnessed by a package depending both on the peer name and on the constrained name, which is precisely the condition under which the reduction emits a core edge for it (peer constraints without such a witness leave no trace and cannot be recovered).
For Features, `featureLift_featureReduce` covers all four components (packages, support, feature dependencies, additional dependencies). The feature reduction is the only one that is *not injective on instances*: the automatic base requirement `⟨⟨n,v⟩,f⟩ → n ∋ {v}` it emits for every grounded support fact is structurally identical to an additional-dependency self-edge of the same shape (the reduction does not tag edges by origin). The mechanisation therefore proves an unconditional normal-form retraction first -- `liftDepsARaw_featureDeps`: the raw lift recovers `Δ_a ∪ baseDeps R support`, i.e. `Δ_a` up to the base-requirement closure, mirroring the shape of the Versions retraction -- and derives `lift = Δ_a` on the nose (`liftDepsA_featureDeps`) by subtracting the base requirements recomputed from the lifted repository and support, under `AddlDepRel.BaseIrredundant`: no additional dependency restates an automatic base requirement (a semantically redundant entry no real ecosystem input contains). The other components assume only `Support.GroundedIn` (supported packages are real; ungrounded facts leave no trace) and the Functional-in-Name analogues `FeatDepRel.FunctionalInName` / `AddlDepRel.FunctionalInName` of the standing Def 3.1.2 condition, needed because featured entries fan out one edge per required feature and are reassembled by `gatherFs` / `gatherAFs`. This required adding a partial inverse `tryFeaturedN` for the featured-name constructor to `HasFeatureNames`.
For Virtual packages, `lift ∘ reduce = id` is false on principle: the reduction keeps only *real* direct dependee versions (non-real versions in a with-provider entry leave no trace), so the mechanisation proves the `restrictReal`-normalised statement instead, mirroring the Versions retraction: `virtualLift_virtualReduce` recovers `(R, Δ.restrictReal R)`. The dependency component `liftDeps_virtualDeps` recovers no-provider entries edge-locally and reassembles a with-provider entry's real version set from the selector→direct edges (`gatherVS`), assuming the standing Functional-in-Name normalisation and `ProvidesRel.NoSelfProvides` — no package provides its own name (a self-provider's selector→provider edge is structurally identical to a selector→direct edge, so the direct versions could not otherwise be separated from the providers). The provides relation itself is not recoverable: the version-or-top guard of a provides entry is not carried by any edge, so distinct guards matching the same dependencies reduce identically. This required adding partial inverses `trySelectorN` / `tryProviderV` to `HasVirtualNames` / `HasVirtualVersions`.
For Package formulae, no retraction onto formulae exists even up to NNF: `encodeNNF` erases the conjunction structure (a conjunction's encoding is the union of its conjuncts' encodings, so `(p, ψ₁ ∧ ψ₂)` and the pair `(p, ψ₁), (p, ψ₂)` reduce identically, and nested conjunctions collapse to the same edge set). What the reduction preserves — exactly — is each depender's *set of NNF atoms* (positive literals, negative literals, and whole disjunctions, whose synthetic names carry their subformulas), and this is mechanised: `liftAtoms_pfDeps` proves `liftAtoms ∘ pfDeps` recovers the per-depender union of atom sets (`Atom`, `atoms`), with *no* side-conditions (merging is built into the statement), and `satisfies_iff_atoms` shows the atom set is a faithful normal form (a resolution satisfies a formula iff it satisfies every atom). The proof characterises `encodeNNF`'s edge set (`atom edge ∨ nested edge ∨ guard edge`) by induction on `Formula.weight`; guard edges are excluded from decoding by their `{0}` version set, nested edges by their disjunct-witness dependers. This required adding a partial inverse `tryDisjunctN` to `HasPFNames`.
For Variable formulae, the same atom-set retraction is mechanised (`liftAtoms_vfDeps`, again with no side-conditions), with one further normalisation: a variable comparison `x ω y` survives in the reduction only as its *extension* — the set of domain values satisfying it — since the edge carries the evaluated version set and negated comparisons fold into complement operators (a version set does not determine the comparison that produced it). The atom type therefore has a fourth constructor `Atom.var x W` holding the extension `W ⊆ Y_x(x)`, and `satisfies_iff_atoms` shows the atom set is faithful for assignments within the declared variable domains. This required adding partial inverses `tryVarN` / `tryDisjunctN` to `HasVFNames` and `tryVarValV` to `HasVFVersions`.
For version formulae, `Versions/Lifting/Retraction.lean` proves the section direction `vfReduce ∘ liftVFDeps = restrictReal` (a formula is not uniquely determined by its version set, so `lift ∘ reduce = id` does not apply).

## Appendix B -- `DependencyResolution` complexity

The paper's NP-completeness result (Thm 3.1.4) combines NP-hardness -- a polynomial-time reduction from 3SAT -- with NP-membership, which the paper establishes by direct polynomial-time verification of a candidate resolution (root inclusion, dependency closure, version uniqueness).
In Lean we mechanise the reduction's soundness and completeness (below); the polynomial-time bound and the membership verification are argued by inspection in the paper, not formalised.
The SAT encoding in Appendix C is a separate SAT-based solving method (formalised in `SATEncoding.lean`).

| Paper                       | Lean                        | File                         |
| --------------------------- | --------------------------- | ---------------------------- |
| 3SAT instance / clause      | `ThreeClause`, `Literal`    | `Complexity/ThreeSAT.lean`   |
| 3SAT → resolution reduction | `satRedReal` / `satRedDeps` | `Complexity/NPHardness.lean` |
| Reduction soundness         | `satRed_soundness`          | `Complexity/NPHardness.lean` |
| Reduction completeness      | `satRed_completeness`       | `Complexity/NPHardness.lean` |

## Appendix C -- SAT-based resolution

| Paper                                     | Lean                       | File                          |
| ----------------------------------------- | -------------------------- | ----------------------------- |
| Def C.1 Package Calculus SAT Encoding     | `satisfiesEncoding`        | `Complexity/SATEncoding.lean` |
| Thm C.2 Soundness                         | `satEncoding_soundness`    | `Complexity/SATEncoding.lean` |
| Thm C.3 Completeness                      | `satEncoding_completeness` | `Complexity/SATEncoding.lean` |

## Appendix D -- Singular Dependencies

| Paper                                    | Lean                                                                    | File                       |
| ---------------------------------------- | ----------------------------------------------------------------------- | -------------------------- |
| Def D.1 Singular Dependency              | `SingularRel`                                                           | `Extensions/Singular.lean` |
| Def D.2 Singular Dependency Resolution   | `IsSingularResolution` (reduction `singularToCore`, `singular_is_core`) | `Extensions/Singular.lean` |

Defs C.5 and C.6 (resolution ordering, ordered SAT encoding) and Appendix E (build graph, optional dependencies) are definitional discussion with no accompanying theorems, and are not mechanised.
