import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CoframeEvaluations
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameComposites
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CharacterCoframePowers
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Flag evaluation of refined append coframes

The canonical word-to-flag comparison is combined once before taking
coordinates. A polynomial append coframe on any refinement then evaluates
at its composite group lift.
-/

set_option autoImplicit false

noncomputable section
universe u v w

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace SchubertGeometry.RetainedCharacter

open private comparisonCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeComparison
open private comparisonResult comparison_base_finish eval_map_eq equalityRight endpoint_pullback
    from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendPowerFrames
open private polynomialBase from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoordinates
open private appendPolynomialLift appendPolynomialLift_endpoint from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoframes
open private flagComparison from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CoframeEvaluations

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

/-- The canonical flag comparison for a coframe on a word-chart refinement. -/
def flagChartComparison (word : List G.rootBase.support) (n : ℕ)
    {X P : Scheme.{u}} (j : P ⟶ X) (q : X ⟶ bsdhScheme G word)
    (M : X.Modules)
    (W : (pullback q).obj
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word) ≅ M) :
    (pullback ((j ≫ q) ≫ bsdhMap G word)).obj
        (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)) ≅
      (pullback j).obj M :=
  flagComparison j q (bsdhMap G word)
    (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)) M W

variable (word : List G.rootBase.support) (i : G.rootBase.support)
    (V : Over (Spec (.of K))) (g : G.points)
    (a : V ⟶ (oppositeUnipotentVariety G).toOver)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      CategoryTheory.Limits.pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ g)
    (B : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (op B) ⟶ V)

private def appendRefinedCoframeResult (n : ℕ) (ε : Fin 2)
    {X : Scheme.{u}} (P : Over (Spec (.of K)))
    (j : P.left ⟶ X) (q : X ⟶ bsdhScheme G (word ++ [i]))
    (f : P ⟶ polynomialBase B)
    (h : j ≫ q = f.left ≫
      (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c))
    (M : X.Modules)
    (W : (pullback q).obj
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i])) ≅ M) : Prop
          :=
  comparisonResult G (G.positiveRootCharacter ^ n)
    (Y := (Over.mk (bsdhToSpec G (word ++ [i]))).left)
    f h h W.symm (appendPolynomialFrame G word i V g a c hend B p n ⟨ε⟩)
    (bsdhMap G (word ++ [i])) rfl
    (appendPolynomialLift G i V g a B p ε)
    ((appendPolynomialLift_endpoint G word i V g a c hend B p ε).trans
      (Category.assoc (projectiveLinePolynomialChart B ⟨ε⟩)
        (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))).symm)

/-- A refined append coframe evaluates at its polynomial group lift after
transport through the canonical pullback comparisons. -/
theorem appendRefinedCoframe_eval (n : ℕ) (ε : Fin 2)
    {X : Scheme.{u}} (P : Over (Spec (.of K)))
    (j : P.left ⟶ X) (q : X ⟶ bsdhScheme G (word ++ [i]))
    (f : P ⟶ polynomialBase B)
    (h : j ≫ q = f.left ≫
      (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c))
    (M : X.Modules)
    (W : (pullback q).obj
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i])) ≅ M) :
    appendRefinedCoframeResult G word i V g a c hend B p n ε (X := X) P j q f h M W := by
  have hs := appendPolynomialFrame_evaluation G word i V g a c hend B p n ε
  have hr := eval_map_eq G word i V g a c hend B p n ε
  exact comparison_base_finish G (G.positiveRootCharacter ^ n)
    (P := P) (Q := polynomialBase B) (X := X)
    (Y := (Over.mk (bsdhToSpec G (word ++ [i]))).left)
    (N := CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
    f h h rfl W.symm (appendPolynomialFrame G word i V g a c hend B p n ⟨ε⟩)
    (bsdhMap G (word ++ [i])) rfl
    (e' := equalityRight hs) (heq_of_eq hs)
    (appendPolynomialLift G i V g a B p ε)
    ((appendPolynomialLift_endpoint G word i V g a c hend B p ε).trans
      (Category.assoc (projectiveLinePolynomialChart B ⟨ε⟩)
        (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))).symm)
    hr

end SchubertGeometry.RetainedCharacter
