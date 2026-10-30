import OrbitComplexity.SchubertGeometry.LineBundles.Affine.AffineGeneratorDefinitions
import OrbitComplexity.GroupActions.Modules.UnitSquare

/-! # structure-module maps on the invariant polynomial chart -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory GroupActions
universe u

/-- The pullback map of structure modules uses Mathlib's structure-module objects. -/
def structurePullbackUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  letI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom

/-- The map is the hom of the usual pullback-unit isomorphism. -/
theorem structurePullbackUnit_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullbackObjUnitIso f).hom = structurePullbackUnit f :=
  Scheme.Modules.pullbackObjUnitIso_hom f

/-- The affine chart comparison respects the structure-module maps. -/
theorem projectiveAffineUnit (R : Type u) [CommRing R] (c : Rˣ) (b : R) :
    (restrictPullbackIso (projectiveLinePolynomialChart R ⟨0⟩)
      (projectiveAffineCoordinate R c b) (projectiveAffineMorphism R c b)
      (projectiveAffineCoordinate_chart R c b)).hom.app
        (SheafOfModules.unit (projectiveScheme R (ULift.{u} (Fin 2))).ringCatSheaf) ≫
      (Scheme.Modules.pullback (X := Spec (.of (Polynomial R)))
        (Y := Spec (.of (Polynomial R))) (projectiveAffineCoordinate R c b)).map
          (Scheme.Modules.restrictUnitIso (projectiveLinePolynomialChart R ⟨0⟩)).hom ≫
      structurePullbackUnit (projectiveAffineCoordinate R c b) =
    (Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩)).map
        (structurePullbackUnit (projectiveAffineMorphism R c b)) ≫
      (Scheme.Modules.restrictUnitIso (projectiveLinePolynomialChart R ⟨0⟩)).hom := by
  simpa only [structurePullbackUnit_eq] using
    (restrictPullbackIso_unit (X := Spec (.of (Polynomial R)))
      (Y := projectiveScheme R (ULift.{u} (Fin 2)))
      (projectiveLinePolynomialChart R ⟨0⟩)
      (projectiveAffineCoordinate R c b) (projectiveAffineMorphism R c b)
      (projectiveAffineCoordinate_chart R c b))

end SchubertGeometry.ProjectiveLine
