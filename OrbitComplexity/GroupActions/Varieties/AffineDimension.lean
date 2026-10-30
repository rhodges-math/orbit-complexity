import OrbitComplexity.GroupActions.Varieties.Dimension
import OrbitComplexity.GroupActions.Varieties.AffineVariety
import Mathlib.RingTheory.KrullDimension.Polynomial

/-! # Dimensions of affine varieties and affine spaces

The dimension of an affine variety is the Krull dimension of its coordinate ring.
Affine space with finitely many coordinates has dimension the number of its coordinates.

## Main results

* `GroupActions.dim_affineVariety`: dimension of the spectrum of a coordinate ring.
* `GroupActions.dim_affineSpaceVariety`: dimension of affine space.
-/

namespace GroupActions

universe u

variable (K A : Type u) [Field K] [CommRing A] [Algebra K A]
  [IsReduced A] [Algebra.FiniteType K A]

/-- The dimension of an affine variety is the Krull dimension of its coordinate ring. -/
theorem dim_affineVariety : (affineVariety K A).dim = ringKrullDim A :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

/-- Affine space with finitely many coordinates has dimension the number of coordinates. -/
theorem dim_affineSpaceVariety (ι : Type u) [Finite ι] :
    (affineSpaceVariety K ι).dim = Nat.card ι := by
  rw [affineSpaceVariety, dim_affineVariety,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    zero_add]

end GroupActions
