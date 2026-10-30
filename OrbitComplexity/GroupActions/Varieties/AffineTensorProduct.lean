import OrbitComplexity.GroupActions.Varieties.AffineMorphisms
import OrbitComplexity.GroupActions.Varieties.AffineProduct
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Affine tensor products as products over the field

The spectrum of a tensor algebra is the product of its two affine varieties. The
comparison preserves projections and identifies its rational points with pairs of points.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory Opposite
open scoped TensorProduct
namespace GroupActions
noncomputable section
universe u
variable (K A B : Type u) [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [IsReduced A] [IsReduced B] [IsReduced (A ⊗[K] B)]
  [Algebra.FiniteType K A] [Algebra.FiniteType K B] [Algebra.FiniteType K (A ⊗[K] B)]

/-- The spectrum of the tensor algebra is the categorical product of the affine factors. -/
def affineTensorIso : (affineVariety K (A ⊗[K] B)).toOver ≅
    (affineVariety K A).toOver ⊗ (affineVariety K B).toOver :=
  Over.isoMk (pullbackSpecIso K A B).symm (by
    change (pullbackSpecIso K A B).inv ≫
      (Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K B))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K A))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (A ⊗[K] B)))
    rw [← Category.assoc, pullbackSpecIso_inv_fst]
    change Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (A ⊗[K] B)))
    rw [← Spec.map_comp]
    rfl)

/-- The affine tensor-product comparison preserves the first projection. -/
theorem affineTensorIso_fst : (affineTensorIso K A B).hom ≫
    fst (affineVariety K A).toOver (affineVariety K B).toOver =
      affineMorphism (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B) := by
  apply Over.OverMorphism.ext
  exact pullbackSpecIso_inv_fst K A B

/-- The affine tensor-product comparison preserves the second projection. -/
theorem affineTensorIso_snd : (affineTensorIso K A B).hom ≫
    snd (affineVariety K A).toOver (affineVariety K B).toOver =
      affineMorphism (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B) := by
  apply Over.OverMorphism.ext
  exact pullbackSpecIso_inv_snd K A B

/-- The affine tensor-product comparison takes a rational point to its pair of factor points. -/
theorem affineTensorIso_points (p : (affineVariety K (A ⊗[K] B)).points) :
    (affineVariety K (A ⊗[K] B)).pointsEquivOverHom p ≫ (affineTensorIso K A B).hom =
      lift ((affineVariety K A).pointsEquivOverHom (affineProductPointsEquiv K A B p).1)
        ((affineVariety K B).pointsEquivOverHom (affineProductPointsEquiv K A B p).2) := by
  apply Over.OverMorphism.ext
  exact affineProductPointsEquiv_pullback K A B p

end
end GroupActions
