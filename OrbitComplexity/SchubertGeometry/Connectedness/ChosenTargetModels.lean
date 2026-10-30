import OrbitComplexity.SchubertGeometry.Connectedness.CommonTargetObjects
import OrbitComplexity.SchubertGeometry.Connectedness.InitialFlagSource
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.SeparatedStages
import OrbitComplexity.SchubertGeometry.Normality.Coordinates.ChosenClosedInclusion
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Closed models over the prescribed flag model

A finite family of closed subvarieties is retained over one scalar
extension of the specified flag model. The comparisons preserve the
original flag projection and each closed inclusion.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u v

namespace SchubertGeometry

open private comparison_at_stage common_source_flag from
  OrbitComplexity.SchubertGeometry.Connectedness.InitialFlagSource

open private closed_target_stage
  from OrbitComplexity.SchubertGeometry.Connectedness.TargetStageObjects
open private common_objects
  from OrbitComplexity.SchubertGeometry.Connectedness.CommonTargetObjects
open private variety_diagonal
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets

private theorem normalize_target_bases
    {K : Type u} [CommRing K] {I : Type v}
    (S : Subalgebra ℤ K) (Y : Over (Spec (.of K)))
    (X : I → Over (Spec (.of K))) (j : ∀ i, X i ⟶ Y)
    (P : Over (Spec (.of S))) (qP : Y.left ⟶ P.left)
    (start : CoefficientStage S)
    (hdata : closed_target_stage S Y
      (fun i => Over.mk ((j i).left ≫ Y.hom))
      (fun i => Over.homMk (j i).left rfl) P qP start) :
    closed_target_stage S Y X j P qP start := by
  obtain ⟨k, hk, D, iD, qPk, qD, hP, hOld, hD⟩ := hdata
  refine ⟨k, hk, D, iD, qPk, qD, hP, hOld, ?_⟩
  intro i
  obtain ⟨hi, hcart, htriangle, hfp, hcompact, hqs⟩ := hD i
  have hcart' : IsPullback (qD i) (X i).hom (D i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) := by
    change IsPullback (qD i) ((j i).left ≫ Y.hom) (D i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) at hcart
    simpa only [(j i).w] using hcart
  exact ⟨hi, hcart', htriangle, hfp, hcompact, hqs⟩

/-- A finite family of closed flag subvarieties has closed models over one
scalar extension of the specified flag model, with Cartesian comparisons
and the original inclusion and projection equations. -/
theorem exists_chosen_closed_targets
    {K J I : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    [Finite J] [Finite I] (G : ReductiveGroupData K)
    (Z : I → TopologicalSpace.Closeds (flagVariety G).scheme)
    (U : J → (flagVariety G).scheme.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (hcover : (⨆ t, U t) = ⊤)
    (S : Subalgebra ℤ K) (hS : S.FG) (P : Over (Spec (.of S)))
    [CompactSpace P.left] [LocallyOfFinitePresentation P.hom]
    (qF : (flagVariety G).scheme ⟶ P.left)
    (hF : IsPullback qF (flagVariety G).toSpec P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    closed_target_stage S (flagVariety G).toOver
      (fun i => ((flagVariety G).closedSubvariety (Z i)).toOver)
      (fun i => (flagVariety G).closedInclusion (Z i)) P qF start := by
  let X := fun i => ((flagVariety G).closedSubvariety (Z i)).scheme
  let j : ∀ i, X i ⟶ (flagVariety G).scheme :=
    fun i => ((flagVariety G).closedInclusion (Z i)).left
  let : IsAffineHom (pullback.diagonal (terminal.from (flagVariety G).scheme)) :=
    variety_diagonal (flagVariety G)
  let (i : I) : IsAffineHom (pullback.diagonal (terminal.from (X i))) :=
    variety_diagonal ((flagVariety G).closedSubvariety (Z i))
  have hdata := exists_closed_flag_common G Z U hU hcover S hS P qF hF start
  have hmodels := common_objects X j (flagVariety G).toSpec U hU S P qF start hdata
  exact normalize_target_bases S (flagVariety G).toOver
    (fun i => ((flagVariety G).closedSubvariety (Z i)).toOver)
    (fun i => (flagVariety G).closedInclusion (Z i)) P qF start hmodels

end SchubertGeometry
