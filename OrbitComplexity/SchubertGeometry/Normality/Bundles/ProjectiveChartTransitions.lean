import OrbitComplexity.SchubertGeometry.Normality.Transitions.TransitionCore
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BorelActionComparison
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.AppendChart
import Batteries.Tactic.Lint

/-! # Projective coordinates for specified append-chart transitions -/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u v
namespace SchubertGeometry

private theorem conjugate_equation {C : Type*} [Category C] {X Y Z : C}
    (e : X ≅ Y) (a : X ⟶ X) (b : Y ⟶ Y) (f g : X ⟶ Z)
    (hf : f = a ≫ g) (hb : e.inv ≫ a ≫ e.hom = b) :
    e.inv ≫ f = b ≫ e.inv ≫ g := by
  calc
    _ = e.inv ≫ a ≫ g := by rw [hf]
    _ = (e.inv ≫ a ≫ e.hom) ≫ e.inv ≫ g := by simp [Category.assoc]
    _ = _ := by rw [hb]

/-- A Borel transition becomes its affine projective-line coefficient map. -/
theorem projectiveAppendChart_transition {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (G : ReductiveGroupData K) (i : G.rootBase.support)
    (A : CommAlgCat.{u} K) {V W T : Over (Spec (.of K))}
    (p : (algSpec (.of K)).obj (.op A) ⟶ V)
    (q : (algSpec (.of K)).obj (.op A) ⟶ W)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶ T)
    (d : W ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶ T)
    (beta : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver)
    (h : (p ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫ c =
      (overlapTwist (Y := (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) beta).hom ≫
      (q ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫ d) :
    projectiveAppendChart G i A p c =
      ((projectiveLineScalingIso
        (Units.map (simpleBorelCoefficientMap G i A beta).toRingHom.toMonoidHom
          (simpleRootCoefficient G i))).hom ≫
        (projectiveLineTranslationIso (simpleBorelCoefficientMap G i A beta
          ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) *
            simpleRootParameter G))).hom) ≫ projectiveAppendChart G i A q d := by
  let S := (algSpec (.of K)).obj (.op A)
  let Y := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver
  let E := simpleBorelLineIso G i A
  let b := overlapTwist (Y := Y) beta
  have hh : ((p ⊗ₘ 𝟙 Y) ≫ c).left = b.hom.left ≫ ((q ⊗ₘ 𝟙 Y) ≫ d).left := by
    have hh := congrArg (fun z : S ⊗ Y ⟶ T ↦ z.left) h
    simpa only [Over.comp_left, Category.assoc] using hh
  have hb := simpleBorelAction_relative_std G i A beta
  change E.inv ≫ b.hom.left ≫ E.hom = _ at hb
  exact conjugate_equation E b.hom.left _ _ _ hh hb

end SchubertGeometry
