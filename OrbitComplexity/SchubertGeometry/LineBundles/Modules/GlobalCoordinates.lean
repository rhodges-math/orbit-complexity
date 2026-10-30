import OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalGenerators
import OrbitComplexity.SchubertGeometry.LineBundles.Affine.GlobalAffineEndpoint

/-! # Polynomial coordinates of the specified global sections -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GroupActions
universe u

private abbrev line (R : Type u) [CommRing R] : Scheme.{u} := projectiveScheme R (ULift.{u} (Fin 2))

private abbrev affine (R : Type u) [CommRing R] : Scheme.{u} := Spec (.of (Polynomial R))

private abbrev O (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

private theorem chart_adjunction_unit {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] :
    (Scheme.Modules.restrictAdjunction j).homEquiv (O Y) (O X)
        (Scheme.Modules.restrictUnitIso j).hom =
      SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom := by
  change (Scheme.Modules.restrictAdjunction j).unit.app (O Y) ≫
    (Scheme.Modules.pushforward j).map (Scheme.Modules.restrictUnitIso j).hom = _
  ext U x
  change (j.appIso (j ⁻¹ᵁ U)).hom
    (Y.presheaf.map (homOfLE (j.image_preimage_le U)).op x) = j.app U x
  have hw : Y.presheaf.map (homOfLE (j.image_preimage_le U)).op ≫
      (j.appIso (j ⁻¹ᵁ U)).hom = j.app U :=
    (((j.appIso (j ⁻¹ᵁ U)).comp_inv_eq).mp (j.app_appIso_inv U)).symm
  exact ConcreteCategory.congr_hom hw x

private theorem transpose_counit {D E : Type*} [Category D] [Category E]
    {F : D ⥤ E} {G : E ⥤ D} (adj : F ⊣ G) {X : D} {Y : E}
    (m : X ⟶ G.obj Y) :
    adj.homEquiv X Y (F.map m ≫ adj.counit.app Y) = m := by
  rw [← adj.homEquiv_counit]
  exact (adj.homEquiv X Y).apply_symm_apply m

private theorem chart_zero_hom (R : Type u) [CommRing R] (d : ℕ) :
    (projectiveTransitionChart R d ⟨0⟩).hom = leftChartMap R d := rfl

private theorem left_chart_counit (R : Type u) [CommRing R] (d : ℕ) :
    leftChartMap R d =
      (Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩)).map
          (pullback.fst (leftRestriction R) (twistedRestriction R d)) ≫
        (Scheme.Modules.restrictAdjunction
          (projectiveLinePolynomialChart R ⟨0⟩)).counit.app (O (affine R)) := by
  ext U x
  rfl

private theorem chart_adjunction_projection (R : Type u) [CommRing R] (d : ℕ) :
    (Scheme.Modules.restrictAdjunction (projectiveLinePolynomialChart R ⟨0⟩)).homEquiv
        (projectiveTransitionModule R d) (O (affine R))
        (projectiveTransitionChart R d ⟨0⟩).hom =
      pullback.fst (leftRestriction R) (twistedRestriction R d) := by
  let adj : Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩) ⊣
      Scheme.Modules.pushforward (projectiveLinePolynomialChart R ⟨0⟩) :=
    Scheme.Modules.restrictAdjunction (projectiveLinePolynomialChart R ⟨0⟩)
  let m : projectiveTransitionModule R d ⟶
      (Scheme.Modules.pushforward (projectiveLinePolynomialChart R ⟨0⟩)).obj
        (O (affine R)) := pullback.fst (leftRestriction R) (twistedRestriction R d)
  exact (congrArg (adj.homEquiv _ _) (chart_zero_hom R d)).trans
    ((congrArg (adj.homEquiv _ _) (left_chart_counit R d)).trans
      (transpose_counit adj m))

private theorem chart_square (R : Type u) [CommRing R] (d : ℕ)
    (s : O (line R) ⟶ SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d) (f :
      Polynomial R)
    (hs : s ≫ pullback.fst (SchubertGeometry.ProjectiveLine.leftRestriction R)
      (SchubertGeometry.ProjectiveLine.twistedRestriction R d) =
      SheafOfModules.unitToPushforwardObjUnit
          (projectiveLinePolynomialChart R ⟨0⟩).toRingCatSheafHom ≫
        (Scheme.Modules.pushforward (projectiveLinePolynomialChart R ⟨0⟩)).map
          (Scheme.Modules.globalSectionsSmul (O (affine R))
            ((Scheme.ΓSpecIso (.of (Polynomial R))).inv f))) :
    (Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩)).map s ≫
        (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom =
      (Scheme.Modules.restrictUnitIso (projectiveLinePolynomialChart R ⟨0⟩)).hom ≫
        Scheme.Modules.globalSectionsSmul (O (affine R))
          ((Scheme.ΓSpecIso (.of (Polynomial R))).inv f) := by
  let adj : Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩) ⊣
      Scheme.Modules.pushforward (projectiveLinePolynomialChart R ⟨0⟩) :=
    Scheme.Modules.restrictAdjunction (projectiveLinePolynomialChart R ⟨0⟩)
  let q : O (affine R) ⟶ O (affine R) :=
    Scheme.Modules.globalSectionsSmul (O (affine R))
    ((Scheme.ΓSpecIso (.of (Polynomial R))).inv f)
  apply (adj.homEquiv _ _).injective
  have hr : SheafOfModules.unitToPushforwardObjUnit
        (projectiveLinePolynomialChart R ⟨0⟩).toRingCatSheafHom ≫
          (Scheme.Modules.pushforward (projectiveLinePolynomialChart R ⟨0⟩)).map q =
      adj.homEquiv _ _
        ((Scheme.Modules.restrictUnitIso (projectiveLinePolynomialChart R ⟨0⟩)).hom ≫ q) :=
    (congrArg (fun m => m ≫ (Scheme.Modules.pushforward
      (projectiveLinePolynomialChart R ⟨0⟩)).map q)
        (chart_adjunction_unit (projectiveLinePolynomialChart R ⟨0⟩))).symm.trans
      (adj.homEquiv_naturality_right _ q).symm
  exact (adj.homEquiv_naturality_left s
      (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom).trans
    ((congrArg (fun m => s ≫ m) (chart_adjunction_projection R d)).trans
      (hs.trans hr))

/-- The ordinary monomial has its stated polynomial multiplier in the first chart. -/
theorem projectiveMonomial_left (R : Type u) [CommRing R]
    (d k : ℕ) (hk : k ≤ d) :
    (Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩)).map
        (projectiveMonomialSection R d k hk) ≫
          (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom =
      (Scheme.Modules.restrictUnitIso (projectiveLinePolynomialChart R ⟨0⟩)).hom ≫
        Scheme.Modules.globalSectionsSmul (O (affine R))
          ((Scheme.ΓSpecIso (.of (Polynomial R))).inv (Polynomial.X ^ k)) := by
  apply chart_square R d (projectiveMonomialSection R d k hk) (Polynomial.X ^ k)
  unfold projectiveMonomialSection
  exact pullback.lift_fst ..

/-- The transformed endpoint has its affine polynomial multiplier in the first chart. -/
theorem projectiveAffineEndpoint_left (R : Type u) [CommRing R]
    (d : ℕ) (c b : R) :
    (Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩)).map
        (projectiveAffineEndpoint R d c b) ≫
          (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom =
      (Scheme.Modules.restrictUnitIso (projectiveLinePolynomialChart R ⟨0⟩)).hom ≫
        Scheme.Modules.globalSectionsSmul (O (affine R))
          ((Scheme.ΓSpecIso (.of (Polynomial R))).inv
            ((Polynomial.C c * Polynomial.X + Polynomial.C b) ^ d)) := by
  apply chart_square R d (projectiveAffineEndpoint R d c b)
    ((Polynomial.C c * Polynomial.X + Polynomial.C b) ^ d)
  unfold projectiveAffineEndpoint
  exact pullback.lift_fst ..

end SchubertGeometry.ProjectiveLine
