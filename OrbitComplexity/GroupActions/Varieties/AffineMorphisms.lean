import OrbitComplexity.GroupActions.Varieties.AffineVariety
import OrbitComplexity.GroupActions.Varieties.Morphisms

/-! # Morphisms between affine varieties

A homomorphism of coordinate algebras gives a morphism of affine varieties. On rational
points it acts by composition of algebra homomorphisms.

## Main definitions

* `GroupActions.affineMorphism`: the morphism induced by an algebra homomorphism.

## Main results

* `GroupActions.affineMorphism_points`: the induced map on algebra-valued coordinates.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K A B C : Type u} [Field K] [CommRing A] [CommRing B] [CommRing C]
  [Algebra K A] [Algebra K B] [Algebra K C]
  [IsReduced A] [IsReduced B] [IsReduced C]
  [Algebra.FiniteType K A] [Algebra.FiniteType K B] [Algebra.FiniteType K C]

/-- An algebra homomorphism induces a morphism of affine varieties in the reverse direction. -/
def affineMorphism (f : A →ₐ[K] B) :
    (affineVariety K B).toOver ⟶ (affineVariety K A).toOver :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        Spec.map (CommRingCat.ofHom (algebraMap K B))
    rw [← Spec.map_comp]
    congr 1
    ext k
    exact f.commutes k)

/-- The induced map on rational points composes the point with the coordinate map. -/
theorem affineMorphism_points (f : A →ₐ[K] B) (p : B →ₐ[K] K) :
    Variety.mapPoints (affineMorphism f) ((affineVarietyPointsEquiv K B).symm p) =
      (affineVarietyPointsEquiv K A).symm (p.comp f) := by
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom p.toRingHom) ≫
    Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom (p.comp f).toRingHom)
  rw [← Spec.map_comp]
  rfl

end

end GroupActions
