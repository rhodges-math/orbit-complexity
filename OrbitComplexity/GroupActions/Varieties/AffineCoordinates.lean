import OrbitComplexity.GroupActions.Varieties.AffineMorphisms

/-! # Coordinates of affine morphisms

The coordinate of the image of a rational point is obtained by evaluating the corresponding
polynomial coordinate function at that point.

## Main results

* `GroupActions.affineMorphism_coordinate`: the coordinate formula for an affine-space target.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

universe u

/-- The coordinate of an affine morphism's image is evaluation of its coordinate polynomial. -/
theorem affineMorphism_coordinate {K B ι : Type u} [Field K] [CommRing B] [Algebra K B]
    [IsReduced B] [Algebra.FiniteType K B] [Finite ι]
    (f : MvPolynomial ι K →ₐ[K] B) (p : (affineVariety K B).points) (i : ι) :
    affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints (affineMorphism f) p) i =
      affineVarietyPointsEquiv K B p (f (MvPolynomial.X i)) := by
  let q : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of B) := p.val
  change (Spec.preimage (q ≫ Spec.map (CommRingCat.ofHom f.toRingHom))).hom
    (MvPolynomial.X i) = (Spec.preimage q).hom (f (MvPolynomial.X i))
  rw [Spec.preimage_comp, Spec.preimage_map]
  rfl

end GroupActions
