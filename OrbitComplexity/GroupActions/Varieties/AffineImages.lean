import OrbitComplexity.GroupActions.Varieties.AffineMorphisms
import OrbitComplexity.GroupActions.Varieties.Dimension

/-! # Dimensions of affine images

The closure of an affine morphism has the dimension of the image of its coordinate map.
Rational points give the same closure over an algebraically closed field.

## Main results

* `GroupActions.dim_closure_comap`: spectrum images have the dimension of the coordinate image.
* `GroupActions.affineMorphism_image_dim`: dimension of the rational image of an affine morphism.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

variable {K A B : Type u} [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

/-- The closure of a spectrum image has the dimension of the image coordinate algebra. -/
theorem dim_closure_comap (f : A →ₐ[K] B) :
    topologicalKrullDim (closure (Set.range (PrimeSpectrum.comap f.toRingHom))) =
      ringKrullDim f.range := by
  have hr : Set.range (PrimeSpectrum.comap f.rangeRestrict.toRingHom) =
      closure (Set.range (PrimeSpectrum.comap f.toRingHom)) := by
    have hk : RingHom.ker f.rangeRestrict.toRingHom = RingHom.ker f.toRingHom :=
      AlgHom.ker_rangeRestrict f
    rw [range_comap_of_surjective _ _ f.rangeRestrict_surjective,
      PrimeSpectrum.closure_range_comap, hk]
  rw [← hr]
  have he := (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
    f.rangeRestrict_surjective).isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq
  exact he.symm.trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)

variable [IsReduced A] [IsReduced B]
  [Algebra.FiniteType K A] [Algebra.FiniteType K B] [IsAlgClosed K]

/-- The rational image of an affine morphism has the dimension of its coordinate image. -/
theorem affineMorphism_image_dim (f : A →ₐ[K] B) :
    (affineVariety K A).subsetDim (Set.range (Variety.mapPoints (affineMorphism f))) =
      ringKrullDim f.range := by
  rw [Variety.subsetDim, Variety.pointClosure_range]
  exact dim_closure_comap f

end

end GroupActions
