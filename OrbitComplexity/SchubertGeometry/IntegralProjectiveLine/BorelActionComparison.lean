import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BorelBaseChange
import OrbitComplexity.SchubertGeometry.Cells.Actions

/-! # Agreement of the Borel actions on a simple Schubert variety -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups Opposite
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
universe u v w

private theorem modObj_unique {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {H X Y : C} [MonObj H] [ModObj H Y] (j : X ⟶ Y) [Mono j]
    (a b : ModObj H X) (ha : letI := a; IsModHom H j)
    (hb : letI := b; IsModHom H j) : a = b := by
  apply ModObj.ext
  apply (cancel_mono j).mp
  have h1 : a.smul ≫ j = (H ◁ j) ≫ ModObj.smul (M := H) (X := Y) := by
    let := a
    let := ha
    exact IsModHom.smul_hom
  have h2 : b.smul ≫ j = (H ◁ j) ≫ ModObj.smul (M := H) (X := Y) := by
    let := b
    let := hb
    exact IsModHom.smul_hom
  exact h1.trans h2.symm

private theorem hom_smul_eq {C : Type v} [Category.{w} C] [CartesianMonoidalCategory C]
    {H X Z : C} [MonObj H] (a b : ModObj H X) (he : a = b) (m : Z ⟶ H) (x : Z ⟶ X) :
    (letI := a; m • x) = (letI := b; m • x) := by
  cases he
  rfl

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem simpleBorelAction_eq (i : G.rootBase.support) :
    simpleBorelAction G i =
      schubertBorelAction G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  have : Mono (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) :=
    Over.mono_of_mono_left _
  exact modObj_unique
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (simpleBorelAction G i) _ (simpleBorelAction_equivariant G i) inferInstance

/-- The standard Borel action over an affine base has its coefficient-ring affine formula. -/
theorem simpleBorelAction_relative_std (i : G.rootBase.support)
    (A : CommAlgCat.{u} K)
    (beta : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) :
    (simpleBorelLineIso G i A).inv ≫
      (lift
        (fst ((algSpec (.of K)).obj (.op A))
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver)
        ((fst ((algSpec (.of K)).obj (.op A))
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ≫ beta) •
          snd ((algSpec (.of K)).obj (.op A))
            (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver)).left ≫
      (simpleBorelLineIso G i A).hom =
        (projectiveLineScalingIso
          (Units.map (simpleBorelCoefficientMap G i A beta).toRingHom.toMonoidHom
            (simpleRootCoefficient G i))).hom ≫
        (projectiveLineTranslationIso ((simpleBorelCoefficientMap G i A beta)
          ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) *
            simpleRootParameter G))).hom := by
  let S := (algSpec (.of K)).obj (.op A)
  let Y := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver
  have hs := hom_smul_eq (simpleBorelAction G i)
    (schubertBorelAction G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (simpleBorelAction_eq G i) (fst S Y ≫ beta) (snd S Y)
  have ht := congrArg (fun y => (simpleBorelLineIso G i A).inv ≫
    (lift (fst S Y) y).left ≫ (simpleBorelLineIso G i A).hom) hs
  exact ht.symm.trans (simpleBorelAction_relative G i A beta)

end SchubertGeometry
end
