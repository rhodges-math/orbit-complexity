import OrbitComplexity.SchubertGeometry.LineBundles.Affine.GlobalAffineAction

/-! # Transformation of existing sections by the global affine line map -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GroupActions
universe u
private abbrev line (R : Type u) [CommRing R] := projectiveScheme R (ULift.{u} (Fin 2))
private abbrev affine (R : Type u) [CommRing R] := Spec (.of (Polynomial R))
private abbrev O (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- A global section transforms by the polynomial-chart pullback of its coefficient. -/
theorem projectiveAffineLineMap_section (R : Type u) [CommRing R]
    (d : ℕ) (c : Rˣ) (b : R)
    (s t : O (line R) ⟶ SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d) (x y :
      Polynomial R)
    (hs : (Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩)).map s ≫
        (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom =
      (Scheme.Modules.restrictUnitIso (projectiveLinePolynomialChart R ⟨0⟩)).hom ≫
        Scheme.Modules.globalSectionsSmul (O (affine R)) ((Scheme.ΓSpecIso (.of (Polynomial R))).inv
          x))
    (ht : (Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩)).map t ≫
        (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom =
      (Scheme.Modules.restrictUnitIso (projectiveLinePolynomialChart R ⟨0⟩)).hom ≫
        Scheme.Modules.globalSectionsSmul (O (affine R)) ((Scheme.ΓSpecIso (.of (Polynomial R))).inv
          y))
    (hxy : (projectiveAffineCoordinate R c b).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial R))).inv x) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv y) :
    (Scheme.Modules.pullback (projectiveAffineMorphism R c b)).map s ≫ projectiveAffineLineMap R d c
      b =
      (Scheme.Modules.pullbackObjUnitIso (projectiveAffineMorphism R c b)).hom ≫ t := by
  have h := projectiveAffineSection_square R d c b s t x y hs ht hxy
  let : Mono (projectiveTransitionEmbed R d) := projectiveTransitionEmbed_mono R d
  apply (cancel_mono (projectiveTransitionEmbed R d)).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun m => (Scheme.Modules.pullback (projectiveAffineMorphism R c b)).map s ≫ m)
      (projectiveAffineLineMap_chart R d c b)).trans h)

end SchubertGeometry.ProjectiveLine
