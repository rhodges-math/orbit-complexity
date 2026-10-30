import Batteries.Tactic.Lint
import Mathlib.AlgebraicGeometry.Noetherian
import OrbitComplexity.SchubertGeometry.Connectedness.CellModelMaps

/-!
# Finite presentation of arithmetic cell maps

Maps from the specified affine cell models to a finite-presentation target over
a coefficient stage are locally of finite presentation and quasi-compact.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting GroupActions ReductiveGroups

noncomputable section

namespace SchubertGeometry.CellContraction

universe u

private theorem affine_base_fp (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (h : Algebra.FinitePresentation R A) :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  apply (LocallyOfFinitePresentation.SpecMap_iff
    (CommRingCat.ofHom (algebraMap R A))).mpr
  change (algebraMap R A).FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  exact h

private theorem affine_base_qc (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R A))) := inferInstance

private theorem stage_base_fp {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) [LocallyOfFinitePresentation a]
    (j : CoefficientStage S) : LocallyOfFinitePresentation (stageScalarModel S a j).hom := by
  change LocallyOfFinitePresentation (pullback.fst
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) a)
  infer_instance

private theorem stage_base_qc {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) [QuasiCompact a]
    (j : CoefficientStage S) : QuasiCompact (stageScalarModel S a j).hom := by
  change QuasiCompact (pullback.fst
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) a)
  infer_instance

private theorem common_base_properties {S X Y : Scheme.{u}} [IsLocallyNoetherian S]
    [CompactSpace X] (a : X ⟶ S) (b : Y ⟶ S)
    [LocallyOfFiniteType a] [LocallyOfFiniteType b]
    (f : X ⟶ Y) (hf : f ≫ b = a) : LocallyOfFinitePresentation f ∧ QuasiCompact f := by
  let : LocallyOfFiniteType (f ≫ b) := by
    simpa only [hf] using (inferInstance : LocallyOfFiniteType a)
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f b
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian b
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian a
  let : IsNoetherian X := ⟨⟩
  exact ⟨inferInstance, inferInstance⟩

attribute [local instance] coefficientAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {R : Subalgebra ℤ K}

/-- Every stage map from a specified arithmetic cell to a finite-presentation
model is locally of finite presentation and quasi-compact. -/
theorem cellStageMap_finitePres (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne))
    (D : Over (Spec (.of R))) [LocallyOfFinitePresentation D.hom]
    (j : CoefficientStage R)
    (f : stageScalarModel R (cellArithmeticBase G a b w hne M) j ⟶
      stageScalarModel R D.hom j) :
    LocallyOfFinitePresentation f.left ∧ QuasiCompact f.left := by
  let : Algebra.FiniteType ℤ j.val := (Subalgebra.fg_iff_finiteType j.val).mp j.property.1
  let : IsNoetherianRing j.val := Algebra.FiniteType.isNoetherianRing ℤ j.val
  let : LocallyOfFinitePresentation (cellArithmeticBase G a b w hne M) :=
    affine_base_fp R M.model M.finitePresentation
  let : QuasiCompact (cellArithmeticBase G a b w hne M) := affine_base_qc R M.model
  let : LocallyOfFinitePresentation
      (stageScalarModel R (cellArithmeticBase G a b w hne M) j).hom :=
    stage_base_fp R (cellArithmeticBase G a b w hne M) j
  let : QuasiCompact (stageScalarModel R (cellArithmeticBase G a b w hne M) j).hom :=
    stage_base_qc R (cellArithmeticBase G a b w hne M) j
  let : LocallyOfFinitePresentation (stageScalarModel R D.hom j).hom :=
    stage_base_fp R D.hom j
  let : CompactSpace (stageScalarModel R (cellArithmeticBase G a b w hne M) j).left :=
    QuasiCompact.compactSpace_of_compactSpace
      (stageScalarModel R (cellArithmeticBase G a b w hne M) j).hom
  exact common_base_properties
    (stageScalarModel R (cellArithmeticBase G a b w hne M) j).hom
    (stageScalarModel R D.hom j).hom f.left f.w

end SchubertGeometry.CellContraction
