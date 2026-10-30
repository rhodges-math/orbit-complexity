import OrbitComplexity.SchubertGeometry.BSDH.Factorization
import OrbitComplexity.SchubertGeometry.BSDH.CellPoints
import OrbitComplexity.SchubertGeometry.Levi.CellComplexity
import OrbitComplexity.GroupActions.Varieties.ClosedImage
/-! # Surjectivity of reduced-word Schubert endpoint morphisms

The endpoint is proper and its rational image contains the dense top Schubert cell.
It is therefore surjective on all scheme points.
-/

open CategoryTheory AlgebraicGeometry
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- A reduced-word BSDH endpoint is surjective onto its Schubert variety. -/
instance bsdhSchubertMap_surjective (word : List G.rootBase.support)
    (hred : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced word) :
    Surjective (bsdhSchubertMap G word hred).left := by
  let w := ReductiveGroups.simpleWeylWord G.rootBase word
  let j := schubertCellOfLE G w w (ReductiveGroups.WeylBruhatLE.refl G.rootBase w)
  have hj : IsDominant j.left := schubertCellOfLE_self_isDominant G w
  apply GroupActions.Variety.surjective_of_dense_points (schubertVariety G w)
    (schubertCell G w) (bsdhSchubertMap G word hred).left j
    ((isDominant_iff _).mp hj)
  intro x
  obtain ⟨p, hp⟩ := bsdhMap_cell_range G word hred ⟨x, rfl⟩
  let y := GroupActions.Variety.mapPoints j x
  have hy : y.val ≫ (schubertInclusion G w).left =
      (GroupActions.Variety.mapPoints (schubertCellInclusion G w) x).val :=
    congrArg Subtype.val
      ((GroupActions.Variety.mapPoints_comp j (schubertInclusion G w) x).symm.trans
        (congrArg (fun f => GroupActions.Variety.mapPoints f x)
          (schubertCellOfLE_comp G w w _)))
  have he : p ≫ (bsdhSchubertMap G word hred).left = y.val := by
    apply (cancel_mono (schubertInclusion G w).left).mp
    exact ((Category.assoc p (bsdhSchubertMap G word hred).left
      (schubertInclusion G w).left).trans
        ((congrArg (fun f => p ≫ f) (bsdhSchubertMap_comp G word hred)).trans hp)).trans
          hy.symm
  refine ⟨p (IsLocalRing.closedPoint K), ?_⟩
  change (p ≫ (bsdhSchubertMap G word hred).left) (IsLocalRing.closedPoint K) = _
  exact congrArg (fun m => m (IsLocalRing.closedPoint K)) he

end SchubertGeometry
