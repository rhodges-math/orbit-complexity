import OrbitComplexity.SchubertGeometry.Normality.Bundles.ProjectiveModelComparison

/-! # Cartesian squares in the specified projective presentations -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
open scoped TensorProduct
noncomputable section
universe u v w
namespace SchubertGeometry

private theorem pullback_presentations {C : Type v} [Category.{w} C]
    {P X Y Z P' X' : C} {f : P ⟶ X} {a : P ⟶ Y} {b : X ⟶ Z} {c : Y ⟶ Z}
    (h : IsPullback f a b c) (eP : P' ≅ P) (eX : X' ≅ X) :
    IsPullback (eP.hom ≫ f ≫ eX.inv) (eP.hom ≫ a) (eX.hom ≫ b) c := by
  apply h.of_iso' eP eX (Iso.refl _) (Iso.refl _)
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · exact (Category.comp_id _).symm
  · exact (Category.comp_id _).symm
  · exact (Category.id_comp c).trans (Category.comp_id c).symm

/-- Model comparison remains Cartesian in both specified projective presentations. -/
theorem projectiveComparison_cartesian {R K A B : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R A] [Algebra K B]
    (e : K ⊗[R] A ≃ₐ[K] B) {X Y : Scheme.{u}}
    (eX : X ≅ projectiveScheme B (ULift.{u} (Fin 2)))
    (eY : Y ≅ projectiveScheme A (ULift.{u} (Fin 2))) :
    IsPullback
      (eX.hom ≫ projectiveCoeffMap (ULift.{u} (Fin 2))
        (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ≫ eY.inv)
      (eX.hom ≫ projectiveToSpec B (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K B)))
      (eY.hom ≫ projectiveToSpec A (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  pullback_presentations (projectiveModel_cartesian e) eX eY

end SchubertGeometry
