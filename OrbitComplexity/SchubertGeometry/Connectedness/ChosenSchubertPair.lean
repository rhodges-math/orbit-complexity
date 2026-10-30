import OrbitComplexity.SchubertGeometry.Connectedness.ChosenTargetModels
import OrbitComplexity.SchubertGeometry.Connectedness.WordPrefixDiagram
import OrbitComplexity.SchubertGeometry.Cells.Opposite
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # A pair of closed Schubert models

An ordinary and an opposite Schubert variety are retained together on one
scalar extension of the prescribed flag model, preserving both inclusions
and the comparison to the flag model.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u

namespace SchubertGeometry

open private finite_affine_opens
  from OrbitComplexity.SchubertGeometry.Connectedness.WordPrefixDiagram

/-- An ordinary and an opposite Schubert variety have closed models over
one scalar extension of the prescribed flag model. Their comparisons are
Cartesian and retain both inclusions and the old flag projection. -/
theorem exists_chosen_schubert_pair
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (v w : G.weylGroup)
    (S : Subalgebra ℤ K) (hS : S.FG) (P : Over (Spec (.of S)))
    [CompactSpace P.left] [LocallyOfFinitePresentation P.hom]
    (qF : (flagVariety G).scheme ⟶ P.left)
    (hF : IsPullback qF (flagVariety G).toSpec P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k)
      (U V : Over (Spec (.of k.val)))
      (i : U ⟶ stageScalarModel S P.hom k)
      (j : V ⟶ stageScalarModel S P.hom k)
      (qPk : (flagVariety G).scheme ⟶ (stageScalarModel S P.hom k).left)
      (qU : (schubertVariety G w).scheme ⟶ U.left)
      (qV : (oppositeSchubertVariety G v).scheme ⟶ V.left),
      IsPullback qPk (flagVariety G).toSpec (stageScalarModel S P.hom k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
      qPk ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
        P.hom = qF ∧
      IsClosedImmersion i.left ∧
      IsPullback qU (schubertVariety G w).toSpec U.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
      qU ≫ i.left = (schubertInclusion G w).left ≫ qPk ∧
      LocallyOfFinitePresentation U.hom ∧ CompactSpace U.left ∧
      QuasiSeparatedSpace U.left ∧
      IsClosedImmersion j.left ∧
      IsPullback qV (oppositeSchubertVariety G v).toSpec V.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
      qV ≫ j.left = (oppositeSchubertInclusion G v).left ≫ qPk ∧
      LocallyOfFinitePresentation V.hom ∧ CompactSpace V.left ∧
      QuasiSeparatedSpace V.left := by
  obtain ⟨J, _, A, hA, hcover⟩ := finite_affine_opens (flagVariety G).scheme
  let Z : ULift.{u} Bool → TopologicalSpace.Closeds (flagVariety G).scheme :=
    fun x => match x.down with
      | false => schubertSupport G w
      | true => oppositeSchubertSupport G v
  obtain ⟨k, hk, D, inc, qPk, qD, hPk, hOld, hD⟩ :=
    exists_chosen_closed_targets G Z A hA hcover S hS P qF hF start
  obtain ⟨hincU, hU, htriU, hfpU, hcompactU, hqsU⟩ := hD ⟨false⟩
  obtain ⟨hincV, hV, htriV, hfpV, hcompactV, hqsV⟩ := hD ⟨true⟩
  exact ⟨k, hk, D ⟨false⟩, D ⟨true⟩, inc ⟨false⟩, inc ⟨true⟩,
    qPk, qD ⟨false⟩, qD ⟨true⟩, hPk, hOld,
    hincU, hU, htriU, hfpU, hcompactU, hqsU,
    hincV, hV, htriV, hfpV, hcompactV, hqsV⟩

end SchubertGeometry
