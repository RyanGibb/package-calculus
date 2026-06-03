These tables map each definition and theorem in the paper to its mechanised counterpart in this development.
All file paths are relative to the `PackageCalculus/` source directory.

Where the paper writes structured names like `⟨n, vs⟩ ∈ N` or `⟨n, f⟩`, the Lean uses dedicated inductive name/version types and `Has*Names` / `Has*Versions` typeclasses to inject them.

The paper states three standing conditions on every dependency relation (Def 3.1.2: Referents Exist, Functional in Name, Non-Empty).
In Lean these appear as explicit hypotheses on the theorems that consume them.

## 3. Modelling the Core

| Paper                                        | Lean                                                   | File                                    |
| -------------------------------------------- | ------------------------------------------------------ | ----------------------------------------|
| Def 3.1.1 Package                            | `Real`, `Package`                                      | `Core/Definition.lean`                  |
| Def 3.1.2 Dependency                         | `DepRel`                                               | `Core/Definition.lean`                  |
| Def 3.1.3 Resolution                         | `IsResolution`                                         | `Core/Definition.lean`                  |
| Thm 3.1.4 `DependencyResolution` NP-complete | see Appendix A below (`satRed_*`)                      | `Complexity/`                           |
| Def 3.2.1 Version Ordering                   | the `[LT V]` / `[DecidableRel (· < ·)]` order on `V`   | used throughout `Versions/Formula.lean` |
| Def 3.2.2 Version Formula                    | `VersionFormula`, `VersionFormula.eval` (`CmpOp.eval`) | `Versions/Formula.lean`                 |
| Def 3.2.3 Version Formula Dependency         | `VFDepRel`                                             | `Versions/Formula.lean`                 |
| Def 3.2.4 Version Formula Resolution         | `IsVFResolution`                                       | `Versions/Formula.lean`                 |
| Def 3.2.5 Version Formula Reduction          | `vfReduce`                                             | `Versions/Reduction/Definition.lean`    |
| Thm 3.2.6 Correctness                        | `vfReduction_correct`                                  | `Versions/Reduction/Correctness.lean`   |

## 4. Extending the Calculus

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
| Thm 4.5.5 Soundness                  | `pkgFormula_soundness`                           | `Extensions/PackageFormula/Reduction/Soundness.lean`    |
| Thm 4.5.6 Completeness               | `pkgFormula_completeness`                        | `Extensions/PackageFormula/Reduction/Completeness.lean` |

### 4.6 Variable Formulae

| Paper                                 | Lean                                                                    | File                                                     |
| ------------------------------------- | ----------------------------------------------------------------------- | -------------------------------------------------------- |
| Def 4.6.1 Variable Formula            | `Formula N V X Y` (in namespace `VarFormula`), dep. relation `VFDepRel` | `Extensions/VariableFormula/Definition.lean`             |
| Def 4.6.2 Variable Formula Resolution | `IsVFResolution`                                                        | `Extensions/VariableFormula/Definition.lean`             |
| Def 4.6.3 Variable Formula Reduction  | `vfReal` / `vfDeps`                                                     | `Extensions/VariableFormula/Reduction/Definition.lean`   |
| Thm 4.6.4 Soundness                   | `varFormula_soundness`                                                  | `Extensions/VariableFormula/Reduction/Soundness.lean`    |
| Thm 4.6.5 Completeness                | `varFormula_completeness`                                               | `Extensions/VariableFormula/Reduction/Completeness.lean` |

### 4.7 Virtual Packages

| Paper                                | Lean                          | File                                             |
| ------------------------------------ | ----------------------------- | ------------------------------------------------ |
| Def 4.7.1 Virtual Package Provides   | `ProvidesRel`                 | `Extensions/Virtual/Definition.lean`             |
| Def 4.7.2 Virtual Package Resolution | `IsVirtualResolution`         | `Extensions/Virtual/Definition.lean`             |
| Def 4.7.3 Virtual Package Reduction  | `virtualReal` / `virtualDeps` | `Extensions/Virtual/Reduction/Definition.lean`   |
| Thm 4.7.4 Soundness                  | `virtual_soundness`           | `Extensions/Virtual/Reduction/Soundness.lean`    |
| Thm 4.7.5 Completeness               | `virtual_completeness`        | `Extensions/Virtual/Reduction/Completeness.lean` |

### 4.8 Singular Dependencies

| Paper                                    | Lean                                                                    | File                       |
| ---------------------------------------- | ----------------------------------------------------------------------- | -------------------------- |
| Def 4.8.1 Singular Dependency            | `SingularRel`                                                           | `Extensions/Singular.lean` |
| Def 4.8.2 Singular Dependency Resolution | `IsSingularResolution` (reduction `singularToCore`, `singular_is_core`) | `Extensions/Singular.lean` |

## 5. Interoperating Across Ecosystems

### 5.1 Composition of Extensions

| Paper                                   | Lean                                              | File                                                        |
| --------------------------------------- | ------------------------------------------------- | ----------------------------------------------------------- |
| Def 5.1.1 Concurrent Feature Resolution | `IsConcurrentFeatureResolution`                   | `Composition/FeatureConcurrent/Definition.lean`             |
| Def 5.1.2 Concurrent Feature Reduction  | `concurrentFeatureReal` / `concurrentFeatureDeps` | `Composition/FeatureConcurrent/Reduction/Definition.lean`   |
| Thm 5.1.3 Soundness                     | `concurrent_feature_soundness`                    | `Composition/FeatureConcurrent/Reduction/Soundness.lean`    |
| Thm 5.1.4 Completeness                  | `concurrent_feature_completeness`                 | `Composition/FeatureConcurrent/Reduction/Completeness.lean` |

### 5.2 Transpiling

The per-extension retraction `lift ∘ reduce = id` claimed in §5.2 is mechanised in each extension's `Lifting/` subdirectory.
`Lifting/Definition.lean` defines `lift`, `Lifting/Retraction.lean` proves the retraction, and `Lifting/{Soundness,Completeness}.lean` show `lift` carries core resolutions back to extension resolutions.
These live under `Extensions/<Extension>/Lifting/` and `Versions/Lifting/`.

## Appendix A -- `DependencyResolution` complexity

The paper's NP-completeness result (Thm 3.1.4) is witnessed by a polynomial-time reduction from 3SAT.
Membership in NP corresponds to the SAT encoding in Appendix B.
In Lean we mechanise the reduction's soundness and completeness (below); the polynomial-time bound and NP-membership are established by inspection, not formalised.

| Paper                       | Lean                        | File                         |
| --------------------------- | --------------------------- | ---------------------------- |
| 3SAT instance / clause      | `ThreeClause`, `Literal`    | `Complexity/ThreeSAT.lean`   |
| 3SAT → resolution reduction | `satRedReal` / `satRedDeps` | `Complexity/NPHardness.lean` |
| Reduction soundness         | `satRed_soundness`          | `Complexity/NPHardness.lean` |
| Reduction completeness      | `satRed_completeness`       | `Complexity/NPHardness.lean` |

## Appendix B -- SAT-based resolution

| Paper                                     | Lean                       | File                          |
| ----------------------------------------- | -------------------------- | ----------------------------- |
| Def B.1 Package Calculus Reduction to SAT | `satisfiesEncoding`        | `Complexity/SATEncoding.lean` |
| Thm B.2 Soundness                         | `satEncoding_soundness`    | `Complexity/SATEncoding.lean` |
| Thm B.3 Completeness                      | `satEncoding_completeness` | `Complexity/SATEncoding.lean` |
