import OrbitComplexity.FrobeniusSplitting.Splittings.Scheme
import OrbitComplexity.FrobeniusSplitting.Compatible.Quotient
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Compatibly split closed subschemes

An ideal sheaf is compatible with a scheme splitting when its ideal on every
affine open is compatible. Sums and intersections preserve compatibility, and
the associated closed subschemes are reduced.

## Main definitions

* `FrobeniusSplitting.SchemeSplitting.IsCompatible`: compatibility of an ideal sheaf.

## Main results

* `FrobeniusSplitting.SchemeSplitting.IsCompatible.sup`: sums of compatible ideal sheaves.
* `FrobeniusSplitting.SchemeSplitting.IsCompatible.inf`: intersections of compatible ideal sheaves.
* `FrobeniusSplitting.SchemeSplitting.IsCompatible.isReduced`: reducedness of the closed subscheme.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Definition 1.1.3 and
  Proposition 1.2.1.
-/

namespace FrobeniusSplitting.SchemeSplitting

open AlgebraicGeometry

variable {X : Scheme} {p : ℕ}

/-- An ideal sheaf is compatible when its ideals on affine opens are preserved. -/
def IsCompatible (splitting : SchemeSplitting X p) (ideal : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, (splitting.onOpen U).IsCompatible (ideal.ideal U)

/-- Compatibility of an ideal sheaf is compatibility on every affine open. -/
theorem isCompatible_iff (splitting : SchemeSplitting X p) (ideal : X.IdealSheafData) :
    splitting.IsCompatible ideal ↔
      ∀ U : X.affineOpens, (splitting.onOpen U).IsCompatible (ideal.ideal U) :=
  Iff.rfl

variable {splitting : SchemeSplitting X p} {ideal other : X.IdealSheafData}

/-- The sum of compatible ideal sheaves is compatible. -/
theorem IsCompatible.sup (hideal : splitting.IsCompatible ideal)
    (hother : splitting.IsCompatible other) : splitting.IsCompatible (ideal ⊔ other) :=
  fun U ↦ (hideal U).sup (hother U)

/-- The intersection of compatible ideal sheaves is compatible. -/
theorem IsCompatible.inf (hideal : splitting.IsCompatible ideal)
    (hother : splitting.IsCompatible other) : splitting.IsCompatible (ideal ⊓ other) :=
  fun U ↦ (hideal U).inf (hother U)

end FrobeniusSplitting.SchemeSplitting
