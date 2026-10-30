import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCoframeComparison
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.ScalarChartCover
import Batteries.Tactic.Lint

/-!
# Comparing coframes on Cartesian chart families

Cartesian squares over an arithmetic cover construct the scalar cover.
Individual coframe comparisons therefore identify the whole scalar coframe.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting.OperatorSheaf
open FrobeniusSplitting.CharacterLine

namespace SchubertGeometry

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Cartesian chart comparisons identify the scalar pullback of a glued
coframe, with the scalar cover constructed from the chart squares. -/
theorem scalarCoframe_eq_of_squares {Y Z : Scheme.{u}} (q : Z ⟶ Y)
    (U : Scheme.OpenCover.{u} Y) (P : U.I₀ → Scheme.{u})
    (j : ∀ i, P i ⟶ Z) (k : ∀ i, P i ⟶ U.X i)
    (h : ∀ i, IsPullback (k i) (j i) (U.f i) q)
    (L : Y.Modules) (F : L ≅ unitModule Y)
    (FK : (Scheme.Modules.pullback q).obj L ≅ unitModule Z)
    (E : ∀ i, (Scheme.Modules.pullback (U.f i)).obj L ≅ unitModule (U.X i))
    (hF : ∀ i, F.hom.over (U.f i).opensRange =
      (coframeOverRange (U.f i) L (E i)).hom)
    (hK : ∀ i, squareFrameIso q (j i) (U.f i) (k i) (h i).w L (E i) =
      (Scheme.Modules.pullback (j i)).mapIso FK ≪≫ pullbackObjUnitIso (j i)) :
    (Scheme.Modules.pullback q).mapIso F ≪≫ pullbackObjUnitIso q = FK := by
  let V := FrobeniusSplitting.scalarChartCover q U P j k h
  exact scalarCoframe_comparison q U V (fun i => i) k (fun i => (h i).w)
    L F FK E hF hK

end SchubertGeometry
