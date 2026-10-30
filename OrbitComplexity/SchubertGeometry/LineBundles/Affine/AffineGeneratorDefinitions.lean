import OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalGenerators
import OrbitComplexity.SchubertGeometry.LineBundles.Affine.GlobalAffineEndpoint
import OrbitComplexity.SchubertGeometry.LineBundles.Affine.AffineChartAction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Affine projective morphisms and their two generator images -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GroupActions
universe u

private abbrev O (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The projective affine morphism has coordinate expression t ↦ c*t+b. -/
def projectiveAffineMorphism (R : Type u) [CommRing R] (c : Rˣ) (b : R) :
    projectiveScheme R (ULift.{u} (Fin 2)) ⟶ projectiveScheme R (ULift.{u} (Fin 2)) :=
  (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso b).hom

/-- The pulled-back ordinary generators map to their transformed global sections. -/
def projectiveAffineGeneratorMap (R : Type u) [CommRing R] (d : ℕ) (c : Rˣ) (b : R) :
    (Scheme.Modules.pullback (projectiveAffineMorphism R c b)).obj
        (O (projectiveScheme R (ULift.{u} (Fin 2))) ⨿ O (projectiveScheme R (ULift.{u} (Fin 2)))) ⟶
      SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d :=
  (PreservesColimitPair.iso (Scheme.Modules.pullback (projectiveAffineMorphism R c b))
      (O (projectiveScheme R (ULift.{u} (Fin 2)))) (O (projectiveScheme R (ULift.{u} (Fin 2))))).inv
        ≫
    coprod.desc
      ((Scheme.Modules.pullbackObjUnitIso (projectiveAffineMorphism R c b)).hom ≫
        projectiveMonomialSection R d 0 (Nat.zero_le _))
      ((Scheme.Modules.pullbackObjUnitIso (projectiveAffineMorphism R c b)).hom ≫
        projectiveAffineEndpoint R d (c : R) b)

end SchubertGeometry.ProjectiveLine
