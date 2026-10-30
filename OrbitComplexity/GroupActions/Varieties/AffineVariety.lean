import OrbitComplexity.GroupActions.Varieties.Basic
import OrbitComplexity.GroupActions.Varieties.AffinePoints
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! # Affine varieties and polynomial charts

The spectrum of a reduced algebra of finite type over a field is a variety.
Polynomial coordinate rings provide the affine spaces used in flag-variety charts.

## Main definitions

* `GroupActions.affineVariety`: the variety associated to a reduced algebra of finite type.
* `GroupActions.affineSpaceVariety`: affine space with a finite coordinate index.

## Main results

* `GroupActions.affineVarietyPointsEquiv`: rational points as algebra homomorphisms.
* `GroupActions.affineSpaceVarietyPointsEquiv`: rational points as coordinate tuples.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

universe u

variable (K A : Type u) [Field K] [CommRing A] [Algebra K A]
  [IsReduced A] [Algebra.FiniteType K A]

/-- The spectrum of a reduced algebra of finite type over a field, as a variety. -/
noncomputable def affineVariety : GroupActions.Variety K where
  scheme := Spec (CommRingCat.of A)
  toSpec := Spec.map (CommRingCat.ofHom (algebraMap K A))
  locallyOfFiniteType := HasRingHomProperty.Spec_iff.mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- Rational points of an affine variety are algebra homomorphisms into the base field. -/
noncomputable def affineVarietyPointsEquiv :
    (affineVariety K A).points ≃ (A →ₐ[K] K) := affinePointsEquiv.symm

variable (ι : Type u) [Finite ι]

/-- Affine space over a field, with coordinates indexed by a finite type. -/
noncomputable def affineSpaceVariety : GroupActions.Variety K :=
  affineVariety K (MvPolynomial ι K)

/-- Rational points of affine space are tuples of elements of its base field. -/
noncomputable def affineSpaceVarietyPointsEquiv :
    (affineSpaceVariety K ι).points ≃ (ι → K) := affineSpacePointsEquiv ι

end GroupActions
