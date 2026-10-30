# Third-party material

Three Lean files of this repository are adapted from Tau Ceti and Mathlib, which are
under the same license as this repository, and keep the copyright notices of their sources. All
other Lean sources under `OrbitComplexity/` are by the author of this repository and under its
license.

## Vendored files

- `OrbitComplexity/ReductiveGroups/Groups/Diagonal/DiagonalMatrixTorus.lean` is adapted from the
  module `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus` of
  [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
  (Copyright 2026 The Tau Ceti contributors).
- `OrbitComplexity/ReductiveGroups/Groups/Representations/GeneralLinearAdjointMatrix.lean` adapts
  the matrix-conjugation proof of `TauCeti/Algebra/AlgebraicGroup/GeneralLinear/Adjoint/Basic.lean`
  of Tau Ceti at commit `ff4727b73ce4a7f24e496b141778838be685f1b5`
  (Copyright 2026 The Tau Ceti contributors).
- `OrbitComplexity/ReductiveGroups/Lie/Basis/Equivalence.lean` follows the proof of
  `Mathlib/Algebra/Lie/Basis/Prod.lean` of
  [Mathlib](https://github.com/leanprover-community/mathlib4) (Copyright 2026 Oliver Nash).

These sources are under the Apache License 2.0, whose text is in [LICENSE](LICENSE). The three
files are rewritten for this library: their statements and proofs use its definitions and
namespaces, and each file names its source in its header.

## Downloaded dependencies

These packages are downloaded by Lake at the revisions pinned in `lakefile.toml` and
`lake-manifest.json`. They are not included in this repository and keep their own
licenses.

- Tau Ceti: [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti), commit
  `48fe7a5f9ba49e3b1c11a72f54f665abc128b36a` (Apache License 2.0).
- Mathlib: [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4), commit
  `b2bf051988bf69448bce88722cc09a05fea31662` (Apache License 2.0).
- Their own dependencies, pinned in `lake-manifest.json`: plausible, LeanSearchClient,
  importGraph, proofwidgets, aesop, Qq, batteries (Apache License 2.0) and Cli (MIT License).

## Project license

This repository is licensed under the Apache License 2.0; see [LICENSE](LICENSE) and
[NOTICE](NOTICE).
