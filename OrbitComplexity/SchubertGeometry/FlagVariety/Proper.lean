import OrbitComplexity.SchubertGeometry.BSDH.CellPoints
import OrbitComplexity.GroupActions.Varieties.ClosedImage
import OrbitComplexity.SchubertGeometry.Cells.Longest

/-! # Properness of the flag variety

The longest-cell endpoint of a proper BSDH scheme has closed dense image. Its
surjectivity descends universal closedness to the flag variety over the field.
-/

open CategoryTheory AlgebraicGeometry
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem bsdhLongest_surjective (word : List G.rootBase.support)
    (hred : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced word)
    (hw : ReductiveGroups.simpleWeylWord G.rootBase word = G.longestElement) :
    Surjective (bsdhMap G word) := by
  apply GroupActions.Variety.surjective_of_dense_points (flagVariety G)
    (schubertCell G G.longestElement) (bsdhMap G word)
    (schubertCellInclusion G G.longestElement) (longestCell_dense G)
  intro z
  have hpoints := bsdhMap_cell_range G word hred
  rw [hw] at hpoints
  obtain ⟨p, hp⟩ := hpoints ⟨z, rfl⟩
  refine ⟨p (IsLocalRing.closedPoint K), ?_⟩
  change (p ≫ bsdhMap G word) (IsLocalRing.closedPoint K) = _
  exact congrArg (fun m => m (IsLocalRing.closedPoint K)) hp

/-- The flag variety of a reductive group is proper over its coefficient field. -/
instance flagVariety_isProper : IsProper (flagVariety G).toSpec := by
  obtain ⟨word, hred, hword⟩ :=
    (ReductiveGroups.weylCoxeterSystem G.rootBase).exists_isReduced G.longestElement
  have hw : ReductiveGroups.simpleWeylWord G.rootBase word = G.longestElement := by
    simpa only [ReductiveGroups.weylCoxeterSystem_wordProd] using hword.symm
  have : Surjective (bsdhMap G word) := bsdhLongest_surjective G word hred hw
  have : UniversallyClosed (bsdhMap G word ≫ (flagVariety G).toSpec) :=
    inferInstanceAs (UniversallyClosed (bsdhToSpec G word))
  have : UniversallyClosed (flagVariety G).toSpec :=
    UniversallyClosed.of_comp_surjective (bsdhMap G word) (flagVariety G).toSpec
  exact {}

end SchubertGeometry
