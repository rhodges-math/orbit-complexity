import OrbitComplexity.SchubertGeometry.LineBundles.Affine.AffineGeneratorDefinitions
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalDetection
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.AdjointEmbedding
import OrbitComplexity.SchubertGeometry.LineBundles.Affine.AffineUnit

/-! # adjoint chart data for affine pullback -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory GroupActions
open scoped MonoidalCategory
universe u

private theorem transpose_counit {D E : Type*} [Category D] [Category E]
    {F : D ⥤ E} {G : E ⥤ D} (adj : F ⊣ G) {X : D} {Y : E}
    (m : X ⟶ G.obj Y) :
    adj.homEquiv X Y (F.map m ≫ adj.counit.app Y) = m := by
  rw [← adj.homEquiv_counit]
  exact (adj.homEquiv X Y).apply_symm_apply m

private theorem chart_zero_hom (R : Type u) [CommRing R] (d : ℕ) :
    (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom =
      leftChartMap R d := rfl

/- The two counits of the restriction adjunction agree componentwise; comparing the whole
morphisms by `rfl` makes the kernel compute in the coordinate rings of the line. -/
private theorem left_chart_counit (R : Type u) [CommRing R] (d : ℕ) :
    leftChartMap R d =
      (Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩)).map
          (projectiveTransitionEmbed R d) ≫
        (Scheme.Modules.restrictAdjunction (projectiveLinePolynomialChart R ⟨0⟩)).counit.app
          (SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf) := by
  ext U x
  rfl

private theorem chart_adjoint_embed (R : Type u) [CommRing R] (d : ℕ) :
    (Scheme.Modules.restrictAdjunction (projectiveLinePolynomialChart R ⟨0⟩)).homEquiv
        (SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d) (SheafOfModules.unit (Spec
          (.of (Polynomial R))).ringCatSheaf)
          (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom =
      projectiveTransitionEmbed R d :=
  (congrArg ((Scheme.Modules.restrictAdjunction (projectiveLinePolynomialChart R ⟨0⟩)).homEquiv
      _ _) (chart_zero_hom R d)).trans
    ((congrArg ((Scheme.Modules.restrictAdjunction (projectiveLinePolynomialChart R ⟨0⟩)).homEquiv
      _ _) (left_chart_counit R d)).trans
      (transpose_counit (Scheme.Modules.restrictAdjunction (projectiveLinePolynomialChart R ⟨0⟩))
        (projectiveTransitionEmbed R d)))

/-- chart adjunction supplies a map with every coefficient-compatible section square. -/
theorem projectiveAffineChartData (R : Type u) [CommRing R] (d : ℕ) (c : Rˣ) (b : R) :
    type_of% (
  adjointGenerator_embed
    (C := (projectiveScheme R (ULift.{u} (Fin 2))).Modules)
    (D := (Spec (.of (Polynomial R))).Modules)
    (F := Scheme.Modules.pullback (projectiveAffineMorphism R c b))
    (H := Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩))
    (K := Scheme.Modules.pullback (X := Spec (.of (Polynomial R)))
      (Y := Spec (.of (Polynomial R))) (projectiveAffineCoordinate R c b))
    (P := Scheme.Modules.pushforward (projectiveLinePolynomialChart R ⟨0⟩))
    (N := (restrictPullbackIso (projectiveLinePolynomialChart R ⟨0⟩)
      (projectiveAffineCoordinate R c b) (projectiveAffineMorphism R c b)
      (projectiveAffineCoordinate_chart R c b)).hom)
    (O := SheafOfModules.unit (projectiveScheme R (ULift.{u} (Fin 2))).ringCatSheaf)
    (A := SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf)
    (r := (Scheme.Modules.restrictUnitIso (projectiveLinePolynomialChart R ⟨0⟩)).hom)
    (ua := structurePullbackUnit (projectiveAffineMorphism R c b))
    (uf := structurePullbackUnit (projectiveAffineCoordinate R c b))
    (projectiveAffineUnit R c b)
    (Scheme.Modules.restrictAdjunction (projectiveLinePolynomialChart R ⟨0⟩))
    (M := SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d)
    (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom
    (projectiveTransitionEmbed R d) (chart_adjoint_embed R d) ) :=
  adjointGenerator_embed
    (C := (projectiveScheme R (ULift.{u} (Fin 2))).Modules)
    (D := (Spec (.of (Polynomial R))).Modules)
    (F := Scheme.Modules.pullback (projectiveAffineMorphism R c b))
    (H := Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩))
    (K := Scheme.Modules.pullback (X := Spec (.of (Polynomial R)))
      (Y := Spec (.of (Polynomial R))) (projectiveAffineCoordinate R c b))
    (P := Scheme.Modules.pushforward (projectiveLinePolynomialChart R ⟨0⟩))
    (N := (restrictPullbackIso (projectiveLinePolynomialChart R ⟨0⟩)
      (projectiveAffineCoordinate R c b) (projectiveAffineMorphism R c b)
      (projectiveAffineCoordinate_chart R c b)).hom)
    (O := SheafOfModules.unit (projectiveScheme R (ULift.{u} (Fin 2))).ringCatSheaf)
    (A := SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf)
    (r := (Scheme.Modules.restrictUnitIso (projectiveLinePolynomialChart R ⟨0⟩)).hom)
    (ua := structurePullbackUnit (projectiveAffineMorphism R c b))
    (uf := structurePullbackUnit (projectiveAffineCoordinate R c b))
    (projectiveAffineUnit R c b)
    (Scheme.Modules.restrictAdjunction (projectiveLinePolynomialChart R ⟨0⟩))
    (M := SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d)
    (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom
    (projectiveTransitionEmbed R d) (chart_adjoint_embed R d)

end SchubertGeometry.ProjectiveLine
