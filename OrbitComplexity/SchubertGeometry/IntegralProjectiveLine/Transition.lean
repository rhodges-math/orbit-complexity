import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Charts
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import TauCeti.AlgebraicGeometry.Modules.GlobalSections
import OrbitComplexity.FrobeniusSplitting.Modules.Sections

/-! # The projective-line module defined by its Laurent transition -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveLine

private def structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private abbrev line (C : Type u) [CommRing C] := projectiveScheme C (ULift.{u} (Fin 2))
private abbrev affine (C : Type u) [CommRing C] := Spec (.of (Polynomial C))
private abbrev overlap (C : Type u) [CommRing C] := Spec (.of (LaurentPolynomial C))
private abbrev chart (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2)) :=
  projectiveLinePolynomialChart C j

private def leftMap (C : Type u) [CommRing C] : overlap C ⟶ affine C :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent)

private def rightMap (C : Type u) [CommRing C] : overlap C ⟶ affine C :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))

private def overlapMap (C : Type u) [CommRing C] : overlap C ⟶ line C :=
  leftMap C ≫ chart C ⟨0⟩

private theorem overlapMap_right (C : Type u) [CommRing C] :
    rightMap C ≫ chart C ⟨1⟩ = overlapMap C :=
  (projectiveLinePolynomial_overlap C).symm

private def chartModule (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2)) :
    (line C).Modules :=
  (Scheme.Modules.pushforward (chart C j)).obj (SheafOfModules.unit (affine C).ringCatSheaf)

private def overlapModule (C : Type u) [CommRing C] : (line C).Modules :=
  (Scheme.Modules.pushforward (overlapMap C)).obj
    (SheafOfModules.unit (overlap C).ringCatSheaf)

/-- Restriction from the first polynomial chart to the Laurent overlap. -/
def leftRestriction (C : Type u) [CommRing C] :
    chartModule C ⟨0⟩ ⟶ overlapModule C :=
  (Scheme.Modules.pushforward (chart C ⟨0⟩)).map
      (SheafOfModules.unitToPushforwardObjUnit (leftMap C).toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp (leftMap C) (chart C ⟨0⟩)).hom.app _

/-- Restriction from the reciprocal polynomial chart to the same overlap. -/
def rightRestriction (C : Type u) [CommRing C] :
    chartModule C ⟨1⟩ ⟶ overlapModule C :=
  (Scheme.Modules.pushforward (chart C ⟨1⟩)).map
      (SheafOfModules.unitToPushforwardObjUnit (rightMap C).toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp (rightMap C) (chart C ⟨1⟩)).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (overlapMap_right C)).hom.app _

private def transitionSection (C : Type u) [CommRing C] (d : ℕ) : Γ(overlap C, ⊤) :=
  (Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv (LaurentPolynomial.T (d : ℤ))

/-- The second-chart restriction multiplied by the transition monomial. -/
def twistedRestriction (C : Type u) [CommRing C] (d : ℕ) :
    chartModule C ⟨1⟩ ⟶ overlapModule C :=
  rightRestriction C ≫ (Scheme.Modules.pushforward (overlapMap C)).map
    (Scheme.Modules.globalSectionsSmul _ (transitionSection C d))

/-- The sheaf of modules obtained by matching the two polynomial charts with transition T^d. -/
def projectiveTransitionModule (C : Type u) [CommRing C] (d : ℕ) :
    (projectiveScheme C (ULift.{u} (Fin 2))).Modules :=
  pullback (leftRestriction C) (twistedRestriction C d)

private abbrev chartCounit (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2)) :=
  ((Scheme.Modules.restrictFunctorAdjCounitIso (chart C j)).app
    (structureModule (affine C))).hom

/-- The specified projection of matched sections onto the first chart. -/
def leftChartMap (C : Type u) [CommRing C] (d : ℕ) :
    (projectiveTransitionModule C d).restrict (chart C ⟨0⟩) ⟶
      structureModule (affine C) :=
  (Scheme.Modules.restrictFunctor (chart C ⟨0⟩)).map
      (pullback.fst (leftRestriction C) (twistedRestriction C d)) ≫
    chartCounit C ⟨0⟩

/-- The specified projection of matched sections onto the second chart. -/
def rightChartMap (C : Type u) [CommRing C] (d : ℕ) :
    (projectiveTransitionModule C d).restrict (chart C ⟨1⟩) ⟶
      structureModule (affine C) :=
  (Scheme.Modules.restrictFunctor (chart C ⟨1⟩)).map
      (pullback.snd (leftRestriction C) (twistedRestriction C d)) ≫
    chartCounit C ⟨1⟩

private instance leftMap_open (C : Type u) [CommRing C] : IsOpenImmersion (leftMap C) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial C)

private def inversionIso (C : Type u) [CommRing C] : overlap C ≅ overlap C :=
  Scheme.Spec.mapIso
    (LaurentPolynomial.invert.toRingEquiv.toCommRingCatIso.op)

private theorem rightMap_eq (C : Type u) [CommRing C] :
    rightMap C = (inversionIso C).hom ≫ leftMap C := by
  change rightMap C = Spec.map (CommRingCat.ofHom
    (LaurentPolynomial.invert : LaurentPolynomial C ≃ₐ[C] LaurentPolynomial C).toRingHom) ≫
      Spec.map (CommRingCat.ofHom Polynomial.toLaurent)
  rw [← Spec.map_comp]
  rfl

private instance rightMap_open (C : Type u) [CommRing C] : IsOpenImmersion (rightMap C) := by
  rw [rightMap_eq]
  infer_instance

private theorem leftMap_range (C : Type u) [CommRing C] :
    (leftMap C).opensRange = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial C) := by
  apply SetLike.coe_injective
  exact PrimeSpectrum.localization_away_comap_range (LaurentPolynomial C) Polynomial.X

private theorem rightMap_range (C : Type u) [CommRing C] :
    (rightMap C).opensRange = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial C) := by
  simpa only [rightMap_eq] using
    (Scheme.Hom.opensRange_comp_of_isIso (inversionIso C).hom (leftMap C)).trans (leftMap_range C)

private instance rightRestriction_local (C : Type u) [CommRing C] :
    IsIso ((Scheme.Modules.restrictFunctor (chart C ⟨0⟩)).map (rightRestriction C)) := by
  have h : ∀ U : (affine C).Opens,
      chart C ⟨1⟩ ⁻¹ᵁ (chart C ⟨0⟩ ''ᵁ U) ≤ (rightMap C).opensRange := by
    intro U
    rw [rightMap_range, ← projectiveLinePolynomial_preimage C ⟨1⟩ ⟨0⟩ (by decide),
      ← projectiveLinePolynomialChart_range]
    exact (chart C ⟨1⟩).preimage_mono ((chart C ⟨0⟩).image_le_opensRange U)
  dsimp only [rightRestriction]
  erw [Functor.map_comp, Functor.map_comp]
  exact IsIso.comp_isIso'
    (FrobeniusSplitting.restriction_unit_isIso (chart C ⟨0⟩) (chart C ⟨1⟩)
      (rightMap C) h)
    (IsIso.comp_isIso'
      ((Scheme.Modules.restrictFunctor (chart C ⟨0⟩)).mapIso
        ((Scheme.Modules.pushforwardComp (rightMap C) (chart C ⟨1⟩)).app
          (SheafOfModules.unit (overlap C).ringCatSheaf))).isIso_hom
      ((Scheme.Modules.restrictFunctor (chart C ⟨0⟩)).mapIso
        ((Scheme.Modules.pushforwardCongr (overlapMap_right C)).app
          (SheafOfModules.unit (overlap C).ringCatSheaf))).isIso_hom)

private instance transitionSmul_isIso (C : Type u) [CommRing C] (d : ℕ) :
    IsIso (Scheme.Modules.globalSectionsSmul
      (structureModule (overlap C)) (transitionSection C d)) := by
  let t : Γ(overlap C, ⊤)ˣ := Units.map
    (Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv.hom
    (unitOfInvertible (LaurentPolynomial.T (R := C) (d : ℤ)))
  change IsIso (Scheme.Modules.globalSectionsSmul
    (structureModule (overlap C)) (t : Γ(overlap C, ⊤)))
  exact Scheme.Modules.isIso_globalSectionsSmul_units _ t

private instance twistedRestriction_local (C : Type u) [CommRing C] (d : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (chart C ⟨0⟩)).map
      (twistedRestriction C d)) := by
  dsimp only [twistedRestriction]
  erw [Functor.map_comp]
  let hT : IsIso (Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (overlap C).ringCatSheaf) (transitionSection C d)) :=
    transitionSmul_isIso C d
  let hP : IsIso ((Scheme.Modules.pushforward (overlapMap C)).map
      (Scheme.Modules.globalSectionsSmul
        (SheafOfModules.unit (overlap C).ringCatSheaf) (transitionSection C d))) :=
    @Functor.map_isIso _ _ _ _ _ _ (Scheme.Modules.pushforward (overlapMap C)) _ hT
  exact IsIso.comp_isIso' (rightRestriction_local C)
    (@Functor.map_isIso _ _ _ _ _ _ (Scheme.Modules.restrictFunctor (chart C ⟨0⟩)) _ hP)

private instance leftRestriction_local (C : Type u) [CommRing C] :
    IsIso ((Scheme.Modules.restrictFunctor (chart C ⟨1⟩)).map (leftRestriction C)) := by
  have h : ∀ U : (affine C).Opens,
      chart C ⟨0⟩ ⁻¹ᵁ (chart C ⟨1⟩ ''ᵁ U) ≤ (leftMap C).opensRange := by
    intro U
    rw [leftMap_range, ← projectiveLinePolynomial_preimage C ⟨0⟩ ⟨1⟩ (by decide),
      ← projectiveLinePolynomialChart_range]
    exact (chart C ⟨0⟩).preimage_mono ((chart C ⟨1⟩).image_le_opensRange U)
  dsimp only [leftRestriction]
  erw [Functor.map_comp]
  exact IsIso.comp_isIso'
    (FrobeniusSplitting.restriction_unit_isIso (chart C ⟨1⟩) (chart C ⟨0⟩)
      (leftMap C) h)
    ((Scheme.Modules.restrictFunctor (chart C ⟨1⟩)).mapIso
      ((Scheme.Modules.pushforwardComp (leftMap C) (chart C ⟨0⟩)).app
        (SheafOfModules.unit (overlap C).ringCatSheaf))).isIso_hom

private theorem mappedFst_isIso {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {X Y Z : A} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] [HasPullback (F.map f) (F.map g)]
    [PreservesLimit (cospan f g) F] [IsIso (F.map g)] :
    IsIso (F.map (pullback.fst f g)) := by
  rw [← PreservesPullback.iso_hom_fst F f g]
  exact IsIso.comp_isIso' (PreservesPullback.iso F f g).isIso_hom
    (inferInstance : IsIso (pullback.fst (F.map f) (F.map g)))


private theorem leftChartMap_isIso (C : Type u) [CommRing C] (d : ℕ) :
    IsIso (leftChartMap C d) :=
  IsIso.comp_isIso'
    (mappedFst_isIso (Scheme.Modules.restrictFunctor (chart C ⟨0⟩))
      (leftRestriction C) (twistedRestriction C d))
    ((Scheme.Modules.restrictFunctorAdjCounitIso (chart C ⟨0⟩)).app
      (structureModule (affine C))).isIso_hom

private def leftChartIso (C : Type u) [CommRing C] (d : ℕ) :
    (projectiveTransitionModule C d).restrict (chart C ⟨0⟩) ≅
      structureModule (affine C) := by
  let : IsIso (leftChartMap C d) := leftChartMap_isIso C d
  exact asIso (leftChartMap C d)

private theorem mappedSnd_isIso {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {X Y Z : A} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] [HasPullback (F.map f) (F.map g)]
    [PreservesLimit (cospan f g) F] [IsIso (F.map f)] :
    IsIso (F.map (pullback.snd f g)) := by
  rw [← PreservesPullback.iso_hom_snd F f g]
  exact IsIso.comp_isIso' (PreservesPullback.iso F f g).isIso_hom
    (inferInstance : IsIso (pullback.snd (F.map f) (F.map g)))


private theorem rightChartMap_isIso (C : Type u) [CommRing C] (d : ℕ) :
    IsIso (rightChartMap C d) :=
  IsIso.comp_isIso'
    (mappedSnd_isIso (Scheme.Modules.restrictFunctor (chart C ⟨1⟩))
      (leftRestriction C) (twistedRestriction C d))
    ((Scheme.Modules.restrictFunctorAdjCounitIso (chart C ⟨1⟩)).app
      (structureModule (affine C))).isIso_hom

private def rightChartIso (C : Type u) [CommRing C] (d : ℕ) :
    (projectiveTransitionModule C d).restrict (chart C ⟨1⟩) ≅
      structureModule (affine C) := by
  let : IsIso (rightChartMap C d) := rightChartMap_isIso C d
  exact asIso (rightChartMap C d)

/-- The transition module is trivial on each of the two standard polynomial charts. -/
def projectiveTransitionChart (C : Type u) [CommRing C] (d : ℕ)
    (j : ULift.{u} (Fin 2)) :
    (projectiveTransitionModule C d).restrict (projectiveLinePolynomialChart C j) ≅
      (SheafOfModules.unit (Spec (.of (Polynomial C))).ringCatSheaf :
        (Spec (.of (Polynomial C))).Modules) := by
  exact Fin.cases
    (motive := fun i : Fin 2 =>
      (projectiveTransitionModule C d).restrict (chart C ⟨i⟩) ≅ structureModule (affine C))
    (leftChartIso C d)
    (fun k => Fin.cases
      (motive := fun i : Fin 1 =>
        (projectiveTransitionModule C d).restrict (chart C ⟨i.succ⟩) ≅
          structureModule (affine C))
      (rightChartIso C d) (fun i => Fin.elim0 i) k) j.down


end SchubertGeometry.ProjectiveLine
