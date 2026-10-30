import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChart
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedGluingSupport
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalCoordinates
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Frames for relative Cartier charts -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GroupActions FrobeniusSplitting FrobeniusSplitting.OperatorSheaf
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

open RelativeGlue

open private line chart unitLine
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

open private structureModule
  from OrbitComplexity.SchubertGeometry.LineBundles.Affine.GlobalAffineEndpoint

private abbrev unitOf (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def auxiliaryFrame (A : Type u) [CommRing A] (d : ℕ) :
    unitLine (A := A) ⟶ ProjectiveLine.projectiveTransitionModule A d :=
  ProjectiveLine.projectiveAffineEndpoint A d 0 1

private theorem auxiliaryFrame_chart_comp (A : Type u) [CommRing A] (d : ℕ) :
    (Scheme.Modules.restrictFunctor (chart A ⟨0⟩)).map (auxiliaryFrame A d) ≫
        (ProjectiveLine.projectiveTransitionChart A d ⟨0⟩).hom =
      (Scheme.Modules.restrictUnitIso (chart A ⟨0⟩)).hom := by
  have h := ProjectiveLine.projectiveAffineEndpoint_left A d 0 1
  simp only [Polynomial.C_0, zero_mul, zero_add, one_pow, map_one, globalSmul_one] at h
  have hnative := h.trans (Category.comp_id _)
  simpa only [auxiliaryFrame, chart, structureModule] using hnative

private theorem iso_from_comp {D : Type*} [Category D] {X Y Z : D}
    {f : X ⟶ Y} {g : Y ⟶ Z} {e : X ⟶ Z}
    (h : f ≫ g = e) [IsIso g] [IsIso e] : IsIso f :=
  IsIso.of_isIso_fac_right h

private theorem auxiliaryFrame_restrict_isIso (A : Type u) [CommRing A] (d : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (chart A ⟨0⟩)).map
      (auxiliaryFrame A d)) := by
  let : IsIso (ProjectiveLine.projectiveTransitionChart A d ⟨0⟩).hom :=
    (ProjectiveLine.projectiveTransitionChart A d ⟨0⟩).isIso_hom
  let : IsIso (Scheme.Modules.restrictUnitIso (chart A ⟨0⟩)).hom :=
    (Scheme.Modules.restrictUnitIso (chart A ⟨0⟩)).isIso_hom
  exact iso_from_comp (auxiliaryFrame_chart_comp A d)

private theorem auxiliaryFrame_over_isIso (A : Type u) [CommRing A] (d : ℕ) :
    IsIso ((auxiliaryFrame A d).over (chart A ⟨0⟩).opensRange) := by
  exact @isIso_over_of_restrict _ _ (chart A ⟨0⟩) inferInstance _ _
    (auxiliaryFrame A d) (auxiliaryFrame_restrict_isIso A d)


end SchubertGeometry.ProjectiveCartier
