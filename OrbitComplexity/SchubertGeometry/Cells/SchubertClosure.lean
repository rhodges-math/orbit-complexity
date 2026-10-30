import OrbitComplexity.SchubertGeometry.Cells.Schubert

/-! # Irreducibility of Schubert closures

The closed reduced closure of an integral Borel orbit is integral.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private def schubertClosureHomeomorph (w : G.weylGroup) :
    (schubertVariety G w).scheme ≃ₜ closure (Set.range (schubertCellInclusion G w).left) :=
  (schubertInclusion G w).left.isEmbedding.toHomeomorph.trans
    (.setCongr (schubertInclusion_range G w))

/-- A Schubert variety is irreducible. -/
instance schubertVarietyIrreducible (w : G.weylGroup) :
    IrreducibleSpace (schubertVariety G w).scheme := by
  have hr : IsIrreducible (Set.range (schubertCellInclusion G w).left) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (schubertCell G w).scheme).image
        (schubertCellInclusion G w).left
        (schubertCellInclusion G w).left.continuous.continuousOn
  have : IrreducibleSpace (closure (Set.range (schubertCellInclusion G w).left)) :=
    isIrreducible_iff_irreducibleSpace.mp hr.closure
  exact (schubertClosureHomeomorph G w).irreducibleSpace_iff.mpr inferInstance

/-- A Schubert variety is integral. -/
instance schubertVarietyIntegral (w : G.weylGroup) : IsIntegral (schubertVariety G w).scheme :=
  isIntegral_of_irreducibleSpace_of_isReduced _

end
end SchubertGeometry
