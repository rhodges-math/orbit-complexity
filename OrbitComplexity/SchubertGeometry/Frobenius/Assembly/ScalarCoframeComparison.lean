import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CoframeRangeRecovery
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.GlobalFrameSquares
import Batteries.Tactic.Lint

/-!
# Scalar comparison of glued coframes

A glued coframe has the prescribed scalar pullback when its comparisons
with a coframe on the scalar scheme agree on an open cover there.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting.OperatorSheaf
open FrobeniusSplitting.CharacterLine
open SchubertGeometry.ProjectiveCartier

namespace SchubertGeometry

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Individual square comparisons on a covering family identify the scalar
pullback of a global coframe with the prescribed coframe. -/
theorem scalarCoframe_comparison {Y Z : Scheme.{u}} (q : Z ⟶ Y)
    (U : Scheme.OpenCover.{u} Y) (V : Scheme.OpenCover.{u} Z)
    (σ : V.I₀ → U.I₀) (k : ∀ i, V.X i ⟶ U.X (σ i))
    (h : ∀ i, k i ≫ U.f (σ i) = V.f i ≫ q)
    (L : Y.Modules) (F : L ≅ unitModule Y)
    (FK : (Scheme.Modules.pullback q).obj L ≅ unitModule Z)
    (E : ∀ i, (Scheme.Modules.pullback (U.f i)).obj L ≅ unitModule (U.X i))
    (hF : ∀ i, F.hom.over (U.f i).opensRange =
      (coframeOverRange (U.f i) L (E i)).hom)
    (hK : ∀ i, squareFrameIso q (V.f i) (U.f (σ i)) (k i) (h i) L (E (σ i)) =
      (Scheme.Modules.pullback (V.f i)).mapIso FK ≪≫ pullbackObjUnitIso (V.f i)) :
    (Scheme.Modules.pullback q).mapIso F ≪≫ pullbackObjUnitIso q = FK := by
  apply coframe_eq_of_chart_pullback V ((Scheme.Modules.pullback q).obj L)
  intro i
  have hlocal := coframe_global_chart_eq (U.f (σ i)) L F (E (σ i)) (hF (σ i))
  have hs := congrArg (squareFrameIso q (V.f i) (U.f (σ i)) (k i) (h i) L) hlocal
  have hg := squareFrameIso_global q (V.f i) (U.f (σ i)) (k i) (h i) L F
  exact hg.symm.trans (hs.trans (hK i))

end SchubertGeometry
