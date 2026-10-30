import OrbitComplexity.SchubertGeometry.Normality.Bundles.InfinityDiagram

/-! # The closed infinity section on a specified projective bundle -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
noncomputable section
universe u
namespace SchubertGeometry

private theorem section_chart_leg {C : Type*} [Category C] {A B P Y : C}
    (s : A ⟶ B) (e : B ≅ P) (t : A ⟶ P) (a : B ⟶ Y)
    (h : s ≫ e.hom = t) : s ≫ a = t ≫ e.inv ≫ a := by
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The affine-transition bundle has a closed infinity section with every
specified projective-chart leg, on its given base and total colimits. -/
theorem projective_bundle_infinity {J R : Type u} [Category.{u} J] [CommRing R]
    (N : J ⥤ CommAlgCat.{u} R) (D : Jᵒᵖ ⥤ Scheme.{u})
    (π : D ⟶ N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)))
    (e : ∀ j, D.obj j ≅ projectiveScheme (N.obj j.unop) (ULift.{u} (Fin 2)))
    (he : ∀ j, π.app j = (e j).hom ≫
      projectiveToSpec (N.obj j.unop) (ULift.{u} (Fin 2)))
    (c : ∀ {j k : Jᵒᵖ}, (j ⟶ k) → (N.obj j.unop)ˣ)
    (a : ∀ {j k : Jᵒᵖ}, (j ⟶ k) → N.obj j.unop)
    (hmap : ∀ {j k : Jᵒᵖ} (f : j ⟶ k), D.map f ≫ (e k).hom =
      (e j).hom ≫ (projectiveLineScalingIso (c f)).hom ≫
        (projectiveLineTranslationIso (a f)).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) (N.map f.unop).hom.toRingHom)
    (cG : Cocone (N.op ⋙ algSpec (.of R))) (hcG : IsColimit cG)
    (cD : Cocone D) (q : cD.pt ⟶ cG.pt.left) [IsSeparated q]
    (hq : ∀ j, cD.ι.app j ≫ q = π.app j ≫ (cG.ι.app j).left) :
    ∃ δ : cG.pt.left ⟶ cD.pt,
      δ ≫ q = 𝟙 _ ∧ IsClosedImmersion δ ∧
      ∀ j, (cG.ι.app j).left ≫ δ =
        projectiveLineSection (N.obj j.unop) (⟨1⟩ : ULift.{u} (Fin 2)) ≫
          (e j).inv ≫ cD.ι.app j := by
  obtain ⟨s, hs, hcoord⟩ := exists_infinity_diagram N D π e he c a hmap
  obtain ⟨δ, hδ, hclosed, hleg⟩ := exists_glued_section N D π cG hcG cD q hq s hs
  refine ⟨δ, hδ, hclosed, fun j ↦ ?_⟩
  exact (hleg j).trans (section_chart_leg
    (A := Spec (.of (N.obj j.unop))) (s.app j) (e j)
    (projectiveLineSection (N.obj j.unop) (⟨1⟩ : ULift.{u} (Fin 2)))
    (cD.ι.app j) (hcoord j))

end SchubertGeometry
