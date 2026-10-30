# Source scope and verification

This repository contains the 2463-module Lean library `OrbitComplexity`, in seven parts: 15 modules
of `OrbitComplexity/FlagVarieties/` (the Bruhat decomposition of invertible matrices), 557 of
`OrbitComplexity/ReductiveGroups/` (reductive groups, root data, Weyl groups and Lie algebras), 91
of `OrbitComplexity/BruhatIntervals/` (Coxeter groups, words and Bruhat intervals), 364 of
`OrbitComplexity/GroupActions/` (algebraic group actions, orbits and complexity), 431 of
`OrbitComplexity/FrobeniusSplitting/` (Frobenius splitting and normality), 892 of
`OrbitComplexity/SchubertGeometry/` (flag varieties, Schubert and Richardson varieties) and 112 of
`OrbitComplexity/Paper/` (the paper), with the root module `OrbitComplexity`. The general libraries
import only Mathlib, Tau Ceti and each other (`SchubertGeometry` imports the other five,
`GroupActions` imports `ReductiveGroups` and `FlagVarieties`, `ReductiveGroups` imports
`FlagVarieties`), and none imports `OrbitComplexity/Paper/`. All local imports are included. Every
module is in the import closure of the root module, and every module other than the 18 entry points
(the root and the `Main` modules) is in the import closure of `OrbitComplexity.Paper.Audit`. Mathlib
(`b2bf051`) and Tau Ceti (`48fe7a5`) are pinned public Lake dependencies and are not included.

## Source preparation

The sources are those of the development tree, unchanged. `LOCAL_MODULES.json` records, for
every module, the path and hash in this release. `LIBRARY_MANIFEST.json` (in the repository root)
records the version, folder and file hashes of each general library.

## Verification records

- `BUILD_CHECK.json`: the full build of this snapshot with `build.py`, in which every local module
  was compiled; the whole-environment axiom audit (the axioms reachable from all declarations of the
  `OrbitComplexity` modules); and the Batteries linters over all of them.
- `ENDPOINT_AUDIT.txt`: the output of the two modules `OrbitComplexity/Paper/CombinatoricsAudit.lean`
  and `OrbitComplexity/Paper/GeometryAudit.lean`, which `OrbitComplexity/Paper/Audit.lean` imports:
  the axioms of every declaration of the statement index.
- `DEPENDENCIES.json`: the pinned Lake packages.
- `LOCAL_MODULES.json`: the module inventory.
- `SOURCE_COMMIT.json`: the commit of the development tree.
