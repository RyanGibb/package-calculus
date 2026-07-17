These tables map each definition and theorem in the paper to its mechanised counterpart in this development.
All file paths are relative to the `PackageCalculus/` source directory.

Where the paper writes structured names like `⟨n, vs⟩ ∈ N` or `⟨n, f⟩`, the Lean uses dedicated inductive name/version types and `Has*Names` / `Has*Versions` typeclasses to inject them.

The paper states one standing condition on every dependency relation: Functional in Name (Def 3.1.2).
In Lean it appears as an explicit hypothesis (`DepRel.FunctionalInName`) on the theorems that consume it.
The paper's normalisation remark -- merging same-name entries per depender by intersecting their version sets -- is mechanised as `DepRel.merge` (`merge_functionalInName`, `merge_resolution_iff`), alongside `DepRel.restrictReal` (`restrictReal_resolution_iff`) for restricting version sets to real packages; both preserve the set of resolutions.

## 3. The Package Calculus

| Paper                                        | Lean                                                   | File                                    |
| -------------------------------------------- | ------------------------------------------------------ | --------------------------------------- |
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

Lifting is mechanised per extension under `Extensions/<Extension>/Lifting/` (and `Versions/Lifting/`): `Definition.lean` defines `lift`, `Retraction.lean` proves the round trip, and `Soundness.lean`/`Completeness.lean` carry core resolutions back to extension resolutions.

| Extension         | Round trip                                          | Mechanised statement                                                      | Side conditions                                                                                                  |
| ----------------- | --------------------------------------------------- | ------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------- |
| Conflict          | `conflictLift_conflictReduce`                       | `lift ∘ reduce = id` (packages, dependencies, conflicts)                  | --                                                                                                               |
| Concurrent        | `concurrentLift_concurrentReduce`                   | `lift ∘ reduce = id` (packages, dependencies)                             | `DepRel.FunctionalInName`                                                                                        |
| Peer              | `peerLift_peerReduce`                               | `lift ∘ reduce = id` (packages, dependencies, peers)                      | `PeerRel.GroundedIn`                                                                                             |
| Feature           | `featureLift_featureReduce`                         | `lift ∘ reduce = id` (packages, support, feature deps, additional deps)   | `Support.GroundedIn`, `FeatDepRel.FunctionalInName`, `AddlDepRel.FunctionalInName`, `AddlDepRel.BaseIrredundant` |
| Virtual           | `virtualLift_virtualReduce`, `liftProv_virtualDeps` | recovers `(R, Δ.restrictReal R)`; provides recovered as its instantiation | `DepRel.FunctionalInName`, `ProvidesRel.NoSelfProvides`                                                          |
| Package formulae  | `liftAtoms_pfDeps`, `satisfies_iff_atoms`           | NNF atom-set normal form (no formula retraction exists)                   | --                                                                                                               |
| Variable formulae | `liftAtoms_vfDeps`, `satisfies_iff_atoms`           | atom-set normal form, comparisons up to extension                         | --                                                                                                               |
| Version formulae  | `vfReduce ∘ liftVFDeps = restrictReal`              | section direction only                                                    | --                                                                                                               |

Where the statement is weaker than `lift ∘ reduce = id`, the loss is syntactic rather than semantic: the lift recovers a normal form that is proven faithful.
Formulae are recovered as their NNF atom sets, and `satisfies_iff_atoms` shows a resolution satisfies a formula iff it satisfies its atoms; a variable comparison is recovered as its extension, which is all evaluation consults; virtual and version-formula dependencies are recovered up to `restrictReal`, which removes only versions no resolution can select.
The Virtual provides relation is likewise recovered as a normal form, its *instantiation* on Δ -- the admissible (provider, name, depender) triples -- and `instantiate_resolution_congr` shows resolutions consult it only through this instantiation; only the guards' behaviour on dependencies outside Δ is lost.
Each side condition's docstring in the Lean states why it is needed.

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

| Paper                                 | Lean                       | File                          |
| ------------------------------------- | -------------------------- | ----------------------------- |
| Def C.1 Package Calculus SAT Encoding | `satisfiesEncoding`        | `Complexity/SATEncoding.lean` |
| Thm C.2 Soundness                     | `satEncoding_soundness`    | `Complexity/SATEncoding.lean` |
| Thm C.3 Completeness                  | `satEncoding_completeness` | `Complexity/SATEncoding.lean` |

## Appendix D -- Singular Dependencies

| Paper                                  | Lean                                                                    | File                       |
| -------------------------------------- | ----------------------------------------------------------------------- | -------------------------- |
| Def D.1 Singular Dependency            | `SingularRel`                                                           | `Extensions/Singular.lean` |
| Def D.2 Singular Dependency Resolution | `IsSingularResolution` (reduction `singularToCore`, `singular_is_core`) | `Extensions/Singular.lean` |

Defs C.5 and C.6 (resolution ordering, ordered SAT encoding) and Appendix E (build graph, optional dependencies) are definitional discussion with no accompanying theorems, and are not mechanised.
