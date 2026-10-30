import OrbitComplexity.FrobeniusSplitting.Cartier.FrameIsomorphism
import OrbitComplexity.FrobeniusSplitting.Cartier.RangeIsomorphism
import OrbitComplexity.FrobeniusSplitting.Cartier.IsoWeights
import OrbitComplexity.FrobeniusSplitting.Cartier.FrameAgreement
import OrbitComplexity.FrobeniusSplitting.Cartier.SectionComp
import OrbitComplexity.FrobeniusSplitting.Cartier.AffineOperators
import OrbitComplexity.FrobeniusSplitting.Cartier.OpenOperators
import OrbitComplexity.FrobeniusSplitting.Cartier.OpenFunctor
import OrbitComplexity.FrobeniusSplitting.Cartier.ChartComposition
import OrbitComplexity.FrobeniusSplitting.Cartier.TraceWeights
import OrbitComplexity.FrobeniusSplitting.Cartier.ModuleGluing
import OrbitComplexity.FrobeniusSplitting.Cartier.SectionTransport
import OrbitComplexity.FrobeniusSplitting.Cartier.HomRestriction
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition

/-! # Coordinates and trace frames on the projective line -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.OperatorSheaf GroupActions
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

private abbrev line (C : Type u) [CommRing C] : Scheme.{u} :=
  projectiveScheme C (ULift.{u} (Fin 2))

private abbrev affine (C : Type u) [CommRing C] : Scheme.{u} := Spec (.of (Polynomial C))

private def base (C : Type u) [CommRing C] : line C ⟶ Spec (.of C) :=
  projectiveToSpec C (ULift.{u} (Fin 2))

private abbrev chart (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2)) :
    affine C ⟶ line C :=
  projectiveLinePolynomialChart C j

private abbrev chartOpen (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2)) :
    (line C).Opens :=
  (chart C j).opensRange

private def chartRangeIso (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2)) :
    affine C ≅ (chartOpen C j).toScheme :=
  (chart C j).isoOpensRange

private def operators (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p] :
    (line C).Modules := operatorModule (sheafFrobenius C p (base C))

private abbrev transitionLine (C : Type u) [CommRing C] (p : ℕ) :
    (line C).Modules :=
  SchubertGeometry.ProjectiveLine.projectiveTransitionModule C (2 * (p - 1))

/-- The transition-line projection to either polynomial-chart pushforward. -/
def projectiveCartierProjection (C : Type u) [CommRing C] (p : ℕ)
    (j : ULift.{u} (Fin 2)) :
    transitionLine C p ⟶ (Scheme.Modules.pushforward (chart C j)).obj
      (SheafOfModules.unit (affine C).ringCatSheaf) :=
  Fin.cases
    (motive := fun i : Fin 2 => transitionLine C p ⟶
      (Scheme.Modules.pushforward (chart C ⟨i⟩)).obj
        (SheafOfModules.unit (affine C).ringCatSheaf))
    (pullback.fst (SchubertGeometry.ProjectiveLine.leftRestriction C)
      (SchubertGeometry.ProjectiveLine.twistedRestriction C (2 * (p - 1))))
    (fun k => Fin.cases
      (motive := fun i : Fin 1 => transitionLine C p ⟶
        (Scheme.Modules.pushforward (chart C ⟨i.succ⟩)).obj
          (SheafOfModules.unit (affine C).ringCatSheaf))
      (pullback.snd (SchubertGeometry.ProjectiveLine.leftRestriction C)
        (SchubertGeometry.ProjectiveLine.twistedRestriction C (2 * (p - 1))))
      (fun i => Fin.elim0 i) k) j.down

private abbrev chartProjection (C : Type u) [CommRing C] (p : ℕ)
    (j : ULift.{u} (Fin 2)) :
    transitionLine C p ⟶ (Scheme.Modules.pushforward (chart C j)).obj
      (SheafOfModules.unit (affine C).ringCatSheaf) := projectiveCartierProjection C p j

/-- The Cartier chart coefficient in the canonical open-range unit frame. -/
def projectiveCartierCoefficient (C : Type u) [CommRing C] (p : ℕ)
    (j : ULift.{u} (Fin 2)) :
    (transitionLine C p).over (chartOpen C j) ⟶
      (SheafOfModules.unit (line C).ringCatSheaf).over (chartOpen C j) :=
  (chartProjection C p j).over (chartOpen C j) ≫ (unitOverRangeIso (chart C j)).inv

private abbrev chartCoefficient (C : Type u) [CommRing C] (p : ℕ)
    (j : ULift.{u} (Fin 2)) :
    (transitionLine C p).over (chartOpen C j) ⟶
      (SheafOfModules.unit (line C).ringCatSheaf).over (chartOpen C j) :=
  projectiveCartierCoefficient C p j

/-- The univariate trace section transported to the polynomial chart's open range. -/
def projectiveCartierTrace (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    [PerfectRing C p] (j : ULift.{u} (Fin 2)) :
    (operators C p).val.obj (op (chartOpen C j)) :=
  let τ : SchemeFrobeniusMap (affine C) p :=
    (univariateTrace (RingSplitting.ofPerfectRing C p)).toSpec (expChar_pos C p)
  let τU : SchemeFrobeniusMap (chartOpen C j).toScheme p :=
    τ.pushforward (chartRangeIso C j).hom
  let τlocal : localOperators (sheafFrobenius C p (base C)) (chartOpen C j) :=
    (openOperatorEquiv C p (base C) (chartOpen C j)).symm τU
  (operatorModuleSections (sheafFrobenius C p (base C)) (chartOpen C j)).symm τlocal

private abbrev traceSection (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    [PerfectRing C p] (j : ULift.{u} (Fin 2)) :
    (operators C p).val.obj (op (chartOpen C j)) := projectiveCartierTrace C p j

private def localFrame (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    [PerfectRing C p] (j : ULift.{u} (Fin 2)) :
    (SheafOfModules.unit (line C).ringCatSheaf).over (chartOpen C j) ⟶
      (operators C p).over (chartOpen C j) :=
  localSectionHom (X := line C) (operators C p) (chartOpen C j) (traceSection C p j)

private def localCartierMap (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    [PerfectRing C p] (j : ULift.{u} (Fin 2)) :
    (transitionLine C p).over (chartOpen C j) ⟶
      (operators C p).over (chartOpen C j) :=
  chartCoefficient C p j ≫ localFrame C p j

private abbrev laurent (C : Type u) [CommRing C] : Scheme.{u} :=
  Spec (.of (LaurentPolynomial C))

private def leftMap (C : Type u) [CommRing C] : laurent C ⟶ affine C :=
  Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial C →+* LaurentPolynomial C))

private instance leftMap_open (C : Type u) [CommRing C] : IsOpenImmersion (leftMap C) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial C)

private def reciprocal (C : Type u) [CommRing C] : laurent C ≅ laurent C :=
  Scheme.Spec.mapIso
    (LaurentPolynomial.invert : LaurentPolynomial C ≃ₐ[C]
      LaurentPolynomial C).toRingEquiv.toCommRingCatIso.op

private def rightMap (C : Type u) [CommRing C] : laurent C ⟶ affine C :=
  (reciprocal C).hom ≫ leftMap C

private instance rightMap_open (C : Type u) [CommRing C] : IsOpenImmersion (rightMap C) := by
  dsimp only [rightMap]
  infer_instance

private def overlapMap (C : Type u) [CommRing C] : laurent C ⟶ line C :=
  leftMap C ≫ chart C ⟨0⟩

private instance overlapMap_open (C : Type u) [CommRing C] :
    IsOpenImmersion (overlapMap C) := by dsimp only [overlapMap]; infer_instance

private abbrev overlapOpen (C : Type u) [CommRing C] : (line C).Opens :=
  chartOpen C ⟨0⟩ ⊓ chartOpen C ⟨1⟩

private theorem overlapMap_right (C : Type u) [CommRing C] :
    rightMap C ≫ chart C ⟨1⟩ = overlapMap C := by
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [← Spec.map_comp]
  exact (projectiveLinePolynomial_overlap C).symm

private theorem overlapMap_range (C : Type u) [CommRing C] :
    (overlapMap C).opensRange = overlapOpen C := by
  dsimp only [overlapOpen, chartOpen, chart]
  rw [projectiveLinePolynomialChart_range, projectiveLinePolynomialChart_range]
  exact projectiveLinePolynomial_inter C

private def overlapRangeIso (C : Type u) [CommRing C] :
    laurent C ≅ (overlapOpen C).toScheme :=
  (overlapMap C).isoOpensRange ≪≫ (line C).isoOfEq (overlapMap_range C)

private theorem overlapRangeIso_hom (C : Type u) [CommRing C] :
    (overlapRangeIso C).hom ≫ (overlapOpen C).ι = overlapMap C := by
  dsimp only [overlapRangeIso, Iso.trans_hom]
  rw [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoOpensRange_hom_ι]

private theorem left_overlap_factor (C : Type u) [CommRing C] :
    (overlapRangeIso C).hom ≫ (line C).homOfLE
        (show overlapOpen C ≤ chartOpen C ⟨0⟩ from inf_le_left) =
      leftMap C ≫ (chartRangeIso C ⟨0⟩).hom := by
  apply (cancel_mono (chartOpen C ⟨0⟩).ι).mp
  dsimp only [chartRangeIso]
  rw [Category.assoc, Scheme.homOfLE_ι, overlapRangeIso_hom,
    Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  rfl

private theorem right_overlap_factor (C : Type u) [CommRing C] :
    (overlapRangeIso C).hom ≫ (line C).homOfLE
        (show overlapOpen C ≤ chartOpen C ⟨1⟩ from inf_le_right) =
      rightMap C ≫ (chartRangeIso C ⟨1⟩).hom := by
  apply (cancel_mono (chartOpen C ⟨1⟩).ι).mp
  dsimp only [chartRangeIso]
  rw [Category.assoc, Scheme.homOfLE_ι, overlapRangeIso_hom,
    Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  exact (overlapMap_right C).symm

private def sectionOperator (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    (U : (line C).Opens) (s : (operators C p).val.obj (op U)) :
    SchemeFrobeniusMap U.toScheme p :=
  openOperatorEquiv C p (base C) U
    (operatorModuleSections (sheafFrobenius C p (base C)) U s)

private theorem traceSection_restrict (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    [PerfectRing C p] (j : ULift.{u} (Fin 2))
    {V : (line C).Opens} (h : V ≤ chartOpen C j) :
    sectionOperator C p V
      (((operators C p).val.map (homOfLE h).op).hom (traceSection C p j)) =
      (((univariateTrace (RingSplitting.ofPerfectRing C p)).toSpec (expChar_pos C p)).pushforward
        (chartRangeIso C j).hom).openPullback ((line C).homOfLE h) := by
  have ht := openOperatorEquiv_restrict C p (base C) h
    (operatorModuleSections (sheafFrobenius C p (base C)) (chartOpen C j)
      (traceSection C p j))
  change sectionOperator C p V
      (((operators C p).val.map (homOfLE h).op).hom (traceSection C p j)) =
    (sectionOperator C p (chartOpen C j) (traceSection C p j)).openPullback
      ((line C).homOfLE h) at ht
  simpa only [sectionOperator, traceSection, projectiveCartierTrace,
    Equiv.apply_symm_apply] using ht

private theorem left_trace_overlap (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    [PerfectRing C p] :
    (sectionOperator C p (overlapOpen C)
      (((operators C p).val.map (homOfLE
        (show overlapOpen C ≤ chartOpen C ⟨0⟩ from inf_le_left)).op).hom
          (traceSection C p ⟨0⟩))).openPullback (overlapRangeIso C).hom =
      (laurentTrace (RingSplitting.ofPerfectRing C p)).toSpec (expChar_pos C p) := by
  rw [traceSection_restrict, ← SchemeFrobeniusMap.openPullback_comp]
  simp only [left_overlap_factor]
  rw [SchemeFrobeniusMap.openPullback_comp]
  have ht := (SchemeFrobeniusMap.operatorIsoEquiv (p := p)
    (chartRangeIso C ⟨0⟩)).left_inv
      ((univariateTrace (RingSplitting.ofPerfectRing C p)).toSpec (expChar_pos C p))
  change (((univariateTrace (RingSplitting.ofPerfectRing C p)).toSpec
    (expChar_pos C p)).pushforward _).openPullback _ = _ at ht
  rw [ht]
  exact traceFrame_toLaurent C p (RingSplitting.ofPerfectRing C p)

private theorem right_trace_overlap (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    [PerfectRing C p] :
    (sectionOperator C p (overlapOpen C)
      (((operators C p).val.map (homOfLE
        (show overlapOpen C ≤ chartOpen C ⟨1⟩ from inf_le_right)).op).hom
          (traceSection C p ⟨1⟩))).openPullback (overlapRangeIso C).hom =
      ((laurentTrace (RingSplitting.ofPerfectRing C p)).toSpec
        (expChar_pos C p)).inputWeight
          ((Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv
            (LaurentPolynomial.C ((-1 : C) ^ (p - 1)) *
              LaurentPolynomial.T (2 * ((p : ℤ) - 1)))) := by
  rw [traceSection_restrict, ← SchemeFrobeniusMap.openPullback_comp]
  simp only [right_overlap_factor]
  rw [SchemeFrobeniusMap.openPullback_comp]
  have ht := (SchemeFrobeniusMap.operatorIsoEquiv (p := p)
    (chartRangeIso C ⟨1⟩)).left_inv
      ((univariateTrace (RingSplitting.ofPerfectRing C p)).toSpec (expChar_pos C p))
  change (((univariateTrace (RingSplitting.ofPerfectRing C p)).toSpec
    (expChar_pos C p)).pushforward _).openPullback _ = _ at ht
  rw [ht]
  dsimp only [rightMap]
  rw [SchemeFrobeniusMap.openPullback_comp]
  have hl : ((univariateTrace (RingSplitting.ofPerfectRing C p)).toSpec
      (expChar_pos C p)).openPullback (leftMap C) =
      (laurentTrace (RingSplitting.ofPerfectRing C p)).toSpec (expChar_pos C p) :=
    traceFrame_toLaurent C p (RingSplitting.ofPerfectRing C p)
  rw [hl]
  exact traceFrame_reciprocal C p (RingSplitting.ofPerfectRing C p)

end SchubertGeometry.ProjectiveCartier
