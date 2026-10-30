import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarPolynomialTransitions
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.AffineFamilies
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Transitions of scalar append charts

The projective append cocone fixes the transition of its polynomial chart.
That transition is transported to the prescribed scalar chart by its two
Cartesian projections; the cocone and the scalar target remain fixed.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial GroupActions

namespace SchubertGeometry.RetainedCharacter

open private affinePolynomialMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOperatorOverlaps

private theorem chart_cocone_triangle {C : Type u} [Category.{v} C]
    {P Q A B V W X : C} (E : P ≅ A) (F : Q ≅ B) (d : Q ⟶ P)
    (lP : P ⟶ X) (lQ : Q ⟶ X) (g : B ⟶ A) (h : W ⟶ V)
    (a : V ⟶ A) (b : W ⟶ B) (hd : d ≫ E.hom = F.hom ≫ g)
    (hc : h ≫ a = b ≫ g) (hl : d ≫ lP = lQ) :
    h ≫ (a ≫ E.inv ≫ lP) = b ≫ F.inv ≫ lQ := by
  have hg : g ≫ E.inv = F.inv ≫ d := by
    calc
      _ = F.inv ≫ (F.hom ≫ g) ≫ E.inv := by
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = F.inv ≫ (d ≫ E.hom) ≫ E.inv :=
        congrArg (fun f => F.inv ≫ f ≫ E.inv) hd.symm
      _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    _ = (h ≫ a) ≫ E.inv ≫ lP := (Category.assoc _ _ _).symm
    _ = (b ≫ g) ≫ E.inv ≫ lP := congrArg (fun f => f ≫ E.inv ≫ lP) hc
    _ = b ≫ F.inv ≫ (d ≫ lP) := by
      simpa only [Category.assoc] using congrArg (fun f => b ≫ f ≫ lP) hg
    _ = _ := congrArg (fun f => b ≫ F.inv ≫ f) hl

private theorem projectiveAffine_polynomial {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a : Bˣ) (b : B) :
    Spec.map (CommRingCat.ofHom (affinePolynomialMap f a b)) ≫
        projectiveLinePolynomialChart A (⟨0⟩ : ULift.{u} (Fin 2)) =
      projectiveLinePolynomialChart B (⟨0⟩ : ULift.{u} (Fin 2)) ≫
        (projectiveLineScalingIso a).hom ≫ (projectiveLineTranslationIso b).hom ≫
          projectiveCoeffMap (ULift.{u} (Fin 2)) f := by
  have h := (projectiveAffineFamily_chart f a b).symm
  change Spec.map (CommRingCat.ofHom (affinePolynomialMap f a b)) ≫
      projectiveLinePolynomialChart A (⟨0⟩ : ULift.{u} (Fin 2)) =
    projectiveLinePolynomialChart B (⟨0⟩ : ULift.{u} (Fin 2)) ≫
      (projectiveBaseChange (ULift.{u} (Fin 2)) f).hom ≫
        ((projectiveBaseChange (ULift.{u} (Fin 2)) f).inv ≫
          (projectiveLineScalingIso a).hom ≫ (projectiveLineTranslationIso b).hom ≫
            projectiveCoeffMap (ULift.{u} (Fin 2)) f) at h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h

/-- The projective cocone and the natural coefficient map construct the
affine transition on the specified scalar append polynomial charts. -/
theorem scalarAppend_chart_transition {S T : Type u}
    [CommRing S] [CommRing T] [Algebra S T] {J : Type v} [Category.{w} J]
    (N : J ⥤ CommAlgCat.{u} S) (M : J ⥤ CommAlgCat.{u} T)
    (μ : N ⋙ forget₂ (CommAlgCat S) CommRingCat ⟶
      M ⋙ forget₂ (CommAlgCat T) CommRingCat)
    (D : Jᵒᵖ ⥤ Scheme.{u})
    (E : ∀ s, D.obj (.op s) ≅ projectiveScheme (N.obj s) (ULift.{u} (Fin 2)))
    (c : Cocone D) {s t : J} (f : s ⟶ t) (a : (N.obj t)ˣ) (b : N.obj t)
    (hd : D.map f.op ≫ (E s).hom = (E t).hom ≫
      (projectiveLineScalingIso a).hom ≫ (projectiveLineTranslationIso b).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) (N.map f).hom.toRingHom)
    (base : c.pt ⟶ Spec (.of S)) {Y : Scheme.{u}}
    (baseT : Y ⟶ Spec (.of T)) (q : Y ⟶ c.pt)
    (hq : IsPullback q baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (KA : Spec (.of (Polynomial (M.obj s))) ⟶ Y)
    (KB : Spec (.of (Polynomial (M.obj t))) ⟶ Y)
    (hAold : KA ≫ q = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (μ.app s).hom)) ≫
      projectiveLinePolynomialChart (N.obj s) ⟨0⟩ ≫ (E s).inv ≫ c.ι.app (.op s))
    (hBold : KB ≫ q = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (μ.app t).hom)) ≫
      projectiveLinePolynomialChart (N.obj t) ⟨0⟩ ≫ (E t).inv ≫ c.ι.app (.op t))
    (hAbase : KA ≫ baseT =
      Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial (M.obj s)))))
    (hBbase : KB ≫ baseT =
      Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial (M.obj t))))) :
    Spec.map (CommRingCat.ofHom (affinePolynomialMap (M.map f).hom.toRingHom
      (Units.map (μ.app t).hom.toMonoidHom a) ((μ.app t).hom b))) ≫ KA = KB := by
  let g := (projectiveLineScalingIso a).hom ≫ (projectiveLineTranslationIso b).hom ≫
    projectiveCoeffMap (ULift.{u} (Fin 2)) (N.map f).hom.toRingHom
  have hold := chart_cocone_triangle (E s) (E t) (D.map f.op)
    (c.ι.app (.op s)) (c.ι.app (.op t)) g
    (Spec.map (CommRingCat.ofHom (affinePolynomialMap (N.map f).hom.toRingHom a b)))
    (projectiveLinePolynomialChart (N.obj s) (⟨0⟩ : ULift.{u} (Fin 2)))
    (projectiveLinePolynomialChart (N.obj t) (⟨0⟩ : ULift.{u} (Fin 2)))
    hd (projectiveAffine_polynomial (N.map f).hom.toRingHom a b) (c.w f.op)
  exact scalarDiagram_chart_transition N M μ f a b base baseT q hq
    (projectiveLinePolynomialChart (N.obj s) ⟨0⟩ ≫ (E s).inv ≫ c.ι.app (.op s))
    (projectiveLinePolynomialChart (N.obj t) ⟨0⟩ ≫ (E t).inv ≫ c.ι.app (.op t))
    KA KB hAold hBold hAbase hBbase hold

end SchubertGeometry.RetainedCharacter
