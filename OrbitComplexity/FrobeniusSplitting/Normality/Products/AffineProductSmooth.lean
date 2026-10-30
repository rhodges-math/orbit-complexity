import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Affine coordinates of smooth product covers

Restricting a smooth total product along an affine open immersion gives a
smooth tensor-product coordinate algebra. The other factor need not be smooth.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct
namespace FrobeniusSplitting
noncomputable section
universe u

/-- The affine-coordinate tensor product of an open part of a smooth product
cover is smooth, smoothness of that open factor. -/
theorem smooth_tensor_of_open_product (K A B : Type u)
    [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (Z : Over (Spec (CommRingCat.of K)))
    (j : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))) ⟶ Z)
    [IsOpenImmersion j.left]
    [Smooth ((Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B))) ⊗ Z).hom)] :
    Algebra.Smooth K (A ⊗[K] B) := by
  let H : Over (Spec (CommRingCat.of K)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B)))
  have : Smooth (H ⊗ Z).hom := inferInstance
  let e : Z ⊗ H ≅ H ⊗ Z := β_ Z H
  have : Smooth (Z ⊗ H).hom := by
    rw [← e.hom.w]
    infer_instance
  let a := Spec.map (CommRingCat.ofHom (algebraMap K A))
  let b := Spec.map (CommRingCat.ofHom (algebraMap K B))
  let p : pullback a b ⟶ (Z ⊗ H).left :=
    pullback.map a b Z.hom b j.left (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]; exact j.w.symm) (by simp)
  have : IsOpenImmersion p := by dsimp only [p]; infer_instance
  have hp : p ≫ (Z ⊗ H).hom = pullback.fst a b ≫ a := by
    change (p ≫ pullback.fst Z.hom b) ≫ Z.hom = _
    dsimp only [p, pullback.map]
    rw [pullback.lift_fst]
    simp only [Category.assoc, j.w]
    rfl
  have hs : Smooth (pullback.fst a b ≫ a) := by
    rw [← hp]
    infer_instance
  let phi := Spec.map (CommRingCat.ofHom (algebraMap K (A ⊗[K] B)))
  have he : (pullbackSpecIso K A B).hom ≫ phi = pullback.fst a b ≫ a :=
    pullbackSpecIso_hom_base K A B
  have : Smooth phi := by
    have : Smooth ((pullbackSpecIso K A B).hom ≫ phi) := by rw [he]; exact hs
    have : Smooth ((pullbackSpecIso K A B).inv ≫
        ((pullbackSpecIso K A B).hom ≫ phi)) := inferInstance
    simpa only [Iso.inv_hom_id_assoc] using this
  exact RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp this)

end
end FrobeniusSplitting
