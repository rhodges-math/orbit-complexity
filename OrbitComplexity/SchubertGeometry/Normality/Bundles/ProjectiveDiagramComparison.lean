import OrbitComplexity.SchubertGeometry.Normality.Bundles.ProjectiveModelComparison
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.AffineFamilies

/-! # Comparison of projective diagrams over the same model coordinates -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
noncomputable section
universe u v w
namespace SchubertGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem coefficient_comp {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) g ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      projectiveCoeffMap (ULift.{u} (Fin 2)) (g.comp f) := by
  unfold projectiveCoeffMap
  rw [← Proj.map_comp]
  congr 1
  apply GradedRingHom.toRingHom_injective
  change (MvPolynomial.map g).comp (MvPolynomial.map f) = MvPolynomial.map (g.comp f)
  apply MvPolynomial.ringHom_ext <;> intro x <;> simp

private theorem comparison_naturality {C : Type v} [Category.{w} C]
    {X₀ X₁ Y₀ Y₁ A₀ A₁ B₀ B₁ : C} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁)
    (eX₀ : X₀ ≅ A₀) (eX₁ : X₁ ≅ A₁) (eY₀ : Y₀ ≅ B₀) (eY₁ : Y₁ ≅ B₁)
    (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (q₀ : A₀ ⟶ B₀) (q₁ : A₁ ⟶ B₁)
    (hf : f ≫ eX₁.hom = eX₀.hom ≫ a) (hg : g ≫ eY₁.hom = eY₀.hom ≫ b)
    (hq : a ≫ q₁ = q₀ ≫ b) :
    f ≫ (eX₁.hom ≫ q₁ ≫ eY₁.inv) = (eX₀.hom ≫ q₀ ≫ eY₀.inv) ≫ g := by
  apply (cancel_mono eY₁.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hg]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hf, Category.assoc, hq]

variable {J : Type v} [Category.{w} J] {R K : Type u} [CommRing R] [CommRing K]
    (N : J ⥤ CommAlgCat.{u} R) (F : J ⥤ CommAlgCat.{u} K)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (DN DF : Jᵒᵖ ⥤ Scheme.{u})
    (eN : ∀ s, DN.obj (.op s) ≅ projectiveScheme (N.obj s) (ULift.{u} (Fin 2)))
    (eF : ∀ s, DF.obj (.op s) ≅ projectiveScheme (F.obj s) (ULift.{u} (Fin 2)))
    (c : ∀ s t, (s ⟶ t) → (N.obj t)ˣ) (a : ∀ s t, (s ⟶ t) → N.obj t)
    (hN : ∀ s t (f : s ⟶ t), DN.map f.op ≫ (eN s).hom = (eN t).hom ≫
      (projectiveLineScalingIso (c s t f)).hom ≫
      (projectiveLineTranslationIso (a s t f)).hom ≫
      projectiveCoeffMap (ULift.{u} (Fin 2)) (N.map f).hom.toRingHom)
    (hF : ∀ s t (f : s ⟶ t), DF.map f.op ≫ (eF s).hom = (eF t).hom ≫
      (projectiveLineScalingIso (Units.map (v.app t).hom.toMonoidHom (c s t f))).hom ≫
      (projectiveLineTranslationIso ((v.app t).hom (a s t f))).hom ≫
      projectiveCoeffMap (ULift.{u} (Fin 2)) (F.map f).hom.toRingHom)

/-- The model evaluations compare every projective transition arrow. -/
def projectiveDiagramComparison : DF ⟶ DN where
  app s := (eF s.unop).hom ≫
    projectiveCoeffMap (ULift.{u} (Fin 2)) (v.app s.unop).hom ≫ (eN s.unop).inv
  naturality := by
    intro s t f
    have hv : (v.app s.unop).hom.comp (N.map f.unop).hom.toRingHom =
        (F.map f.unop).hom.toRingHom.comp (v.app t.unop).hom :=
      congrArg CommRingCat.Hom.hom (v.naturality f.unop)
    have hcoeff :
        projectiveCoeffMap (ULift.{u} (Fin 2)) (F.map f.unop).hom.toRingHom ≫
          projectiveCoeffMap (ULift.{u} (Fin 2)) (v.app t.unop).hom =
        projectiveCoeffMap (ULift.{u} (Fin 2)) (v.app s.unop).hom ≫
          projectiveCoeffMap (ULift.{u} (Fin 2)) (N.map f.unop).hom.toRingHom := by
      rw [coefficient_comp, coefficient_comp, hv]
    have ha := projectiveAffine_coeff (v.app s.unop).hom
      (c t.unop s.unop f.unop) (a t.unop s.unop f.unop)
    apply comparison_naturality (DF.map f) (DN.map f) (eF s.unop) (eF t.unop)
      (eN s.unop) (eN t.unop) _ _ _ _
      (hF t.unop s.unop f.unop) (hN t.unop s.unop f.unop)
    calc
      _ = ((projectiveLineScalingIso
            (Units.map (v.app s.unop).hom.toMonoidHom (c t.unop s.unop f.unop))).hom ≫
          (projectiveLineTranslationIso ((v.app s.unop).hom (a t.unop s.unop f.unop))).hom) ≫
          (projectiveCoeffMap (ULift.{u} (Fin 2)) (v.app s.unop).hom ≫
            projectiveCoeffMap (ULift.{u} (Fin 2)) (N.map f.unop).hom.toRingHom) := by
        simpa only [Category.assoc] using congrArg
          (fun q ↦ ((projectiveLineScalingIso
            (Units.map (v.app s.unop).hom.toMonoidHom (c t.unop s.unop f.unop))).hom ≫
            (projectiveLineTranslationIso ((v.app s.unop).hom
              (a t.unop s.unop f.unop))).hom) ≫ q) hcoeff
      _ = _ := by
        simpa only [Category.assoc] using (congrArg
          (fun q ↦ q ≫ projectiveCoeffMap (ULift.{u} (Fin 2))
            (N.map f.unop).hom.toRingHom) ha)

end SchubertGeometry
