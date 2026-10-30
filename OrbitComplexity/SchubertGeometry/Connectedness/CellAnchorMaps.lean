import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.StageAnchorMaps
import OrbitComplexity.SchubertGeometry.Connectedness.CellAnchorRetention
import OrbitComplexity.SchubertGeometry.Connectedness.CellMapRetention
import OrbitComplexity.SchubertGeometry.Connectedness.RootEndpointMaps

/-!
# Arithmetic anchor arrows of the cell models

The arithmetic cell origin followed by the retained cell map defines an anchor
arrow. Its full scalar-cone comparison is the specified Richardson anchor.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting GroupActions ReductiveGroups

noncomputable section

namespace SchubertGeometry.CellContraction

universe u

attribute [local instance] coefficientAlgebra

private theorem enlarge_family {J : Type*} {A : J → Sort*} {B : J → Prop}
    {P Q : ∀ j : J, A j → Prop}
    (h : ∃ (j : J) (_ : B j) (f : A j), P j f)
    (step : ∀ (j : J) (f : A j), P j f → Q j f) :
    ∃ (j : J) (_ : B j) (f : A j), Q j f := by
  obtain ⟨j, hj, f, hf⟩ := h
  exact ⟨j, hj, f, step j f hf⟩


variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) {R : Subalgebra ℤ K}

/-- The origin of an arithmetic cell model followed by its chosen stage map. -/
def cellArithmeticAnchorMap (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne))
    (D : Over (Spec (.of R))) (i : CoefficientStage R)
    (f : stageScalarModel R (cellArithmeticBase G a b w hne M) i ⟶
      stageScalarModel R D.hom i) :
    stageScalarModel R (𝟙 (Spec (.of R))) i ⟶ stageScalarModel R D.hom i :=
  anchorArrow _ (cellArithmeticStageOrigin G a b w hne M i)
    (cellArithmeticStageOrigin_base G a b w hne M i) f

/-- The arithmetic cell anchor retains the specified Richardson anchor as an
arrow on the full scalar diagram. -/
theorem cellArithmeticAnchorMap_comparison (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne))
    (D : Over (Spec (.of R))) (i : CoefficientStage R)
    (f : stageScalarModel R (cellArithmeticBase G a b w hne M) i ⟶
      stageScalarModel R D.hom i)
    (qD : (richardsonVariety G a b).scheme ⟶ D.left)
    (hD : IsPullback qD (richardsonVariety G a b).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hf : ((cellArithmeticGenericIso G a b w hne M).inv.left ≫
        (modelScalarCone R (cellArithmeticBase G a b w hne M)).π.app (op i)) ≫ f.left =
      (pullback.snd (schubertCellInclusion G w) (richardsonInclusion G a b)).left ≫
        (chosenGenericIso R (richardsonVariety G a b).toOver D.hom qD hD).hom.left ≫
          (modelScalarCone R D.hom).π.app (op i)) :
    (modelScalarCone R (𝟙 (Spec (.of R)))).π.app (op i) ≫
        (cellArithmeticAnchorMap G a b w hne M D i f).left =
      (cellAnchorGenericMap G a b w hne R D qD hD).left ≫
        (modelScalarCone R D.hom).π.app (op i) :=
  anchorArrow_comparison _ _
    (chosenGenericIso R (richardsonVariety G a b).toOver D.hom qD hD)
    (cartesianGenericIso R D (richardsonVariety G a b).toOver qD hD) rfl
    (cellArithmeticStageOrigin G a b w hne M i)
    (cellArithmeticStageOrigin_base G a b w hne M i) f
    (a := cellArithmeticAnchorMap G a b w hne M D i f) rfl
    (g := cellAnchorGenericMap G a b w hne R D qD hD) rfl rfl
    (cellRichardsonAnchor G a b w hne) rfl _ _ _
    (modelScalarCone_base R (𝟙 (Spec (.of R))) i)
    (cellArithmeticStageAnchor_comparison G a b w hne M D.hom i f _ hf)

/-- All nonempty cell models retain their maps and origin anchors at one common
coefficient stage of the specified Richardson model. -/
theorem exists_cellAnchorMaps (a b : G.weylGroup) (hR : R.FG)
    (M : ∀ w : {w : G.weylGroup // Nonempty (cellIntersection G a b w).left},
      ArithmeticContractionModel (R := R)
        (cellContractionAlg G a b w.val) (cellOriginAlg G a b w.val w.property))
    (D : Over (Spec (.of R))) [LocallyOfFinitePresentation D.hom]
    (qD : (richardsonVariety G a b).scheme ⟶ D.left)
    (hD : IsPullback qD (richardsonVariety G a b).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (start : CoefficientStage R) :
    ∃ (j : CoefficientStage R) (_ : start ≤ j)
      (f : ∀ w : {w : G.weylGroup // Nonempty (cellIntersection G a b w).left},
        stageScalarModel R (cellArithmeticBase G a b w.val w.property (M w)) j ⟶
          stageScalarModel R D.hom j),
      ∀ w : {w : G.weylGroup // Nonempty (cellIntersection G a b w).left},
      ((modelScalarCone R (cellArithmeticBase G a b w.val w.property (M w))).π.app (op j) ≫
          (f w).left =
        (cellArithmeticMap G a b w.val w.property (M w) D.hom qD hD).left ≫
          (modelScalarCone R D.hom).π.app (op j)) ∧
      ((((cellArithmeticGenericIso G a b w.val w.property (M w)).inv.left ≫
          (modelScalarCone R (cellArithmeticBase G a b w.val w.property (M w))).π.app (op j)) ≫
          (f w).left =
        (pullback.snd (schubertCellInclusion G w.val) (richardsonInclusion G a b)).left ≫
          (chosenGenericIso R (richardsonVariety G a b).toOver D.hom qD hD).hom.left ≫
            (modelScalarCone R D.hom).π.app (op j))) ∧
      ((modelScalarCone R (𝟙 (Spec (.of R)))).π.app (op j) ≫
          (cellArithmeticAnchorMap G a b w.val w.property (M w) D j (f w)).left =
        (cellAnchorGenericMap G a b w.val w.property R D qD hD).left ≫
          (modelScalarCone R D.hom).π.app (op j)) := by
  exact enlarge_family (exists_cellArithmeticMaps G a b hR M D.hom qD hD start)
    (fun (j : CoefficientStage R)
      (f : ∀ w : {w : G.weylGroup // Nonempty (cellIntersection G a b w).left},
        stageScalarModel R (cellArithmeticBase G a b w.val w.property (M w)) j ⟶
          stageScalarModel R D.hom j) hf
      (w : {w : G.weylGroup // Nonempty (cellIntersection G a b w).left}) =>
      ⟨(hf w).1, (hf w).2,
        cellArithmeticAnchorMap_comparison G a b w.val w.property (M w) D j (f w) qD hD
          (hf w).2⟩)

end SchubertGeometry.CellContraction
