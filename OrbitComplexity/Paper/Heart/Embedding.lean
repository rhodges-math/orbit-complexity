import OrbitComplexity.Paper.Heart.Definition

/-!
# The closed heart inside a Schubert cell

The root-coordinate presentation places the heart as a closed subvariety of its
Schubert cell, with rational flags exactly of the form v wB for v in Vd.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The heart root isomorphism commutes with the two maps to the flag variety. -/
theorem heartIso_hom_comp (I : Set G.rootBase.support) (w : G.weylGroup) :
    (heartIso G I w).hom ≫ heartInclusion G I w = heartRootMorphism G I w :=
  Variety.pointImageIso_hom_comp _ _ _

/-- The I-heart includes into its Schubert cell. -/
def heartCellInclusion (I : Set G.rootBase.support) (w : G.weylGroup) :
    (heart G I w).toOver ⟶ (schubertCell G w).toOver :=
  (heartIso G I w).inv ≫ Vd.inclusion G I w ≫ (schubertCellIso G w).hom

/-- The heart is a closed subvariety of its Schubert cell. -/
instance heartCellInclusion_isClosed (I : Set G.rootBase.support) (w : G.weylGroup) :
    IsClosedImmersion (heartCellInclusion G I w).left := by
  change IsClosedImmersion ((heartIso G I w).inv.left ≫ (Vd.inclusion G I w).left ≫
    (schubertCellIso G w).hom.left)
  infer_instance

/-- The closed heart inclusion factors its locally closed flag inclusion. -/
theorem heartCellInclusion_comp (I : Set G.rootBase.support) (w : G.weylGroup) :
    heartCellInclusion G I w ≫ schubertCellInclusion G w = heartInclusion G I w := by
  simp only [heartCellInclusion, Category.assoc, schubertCellIso_hom_comp]
  change (heartIso G I w).inv ≫ heartRootMorphism G I w = _
  rw [← heartIso_hom_comp, Iso.inv_hom_id_assoc]

private theorem heartInclusion_points_range (I : Set G.rootBase.support) (w : G.weylGroup) :
    Set.range (Variety.mapPoints (heartInclusion G I w)) =
      Set.range (Variety.mapPoints (heartRootMorphism G I w)) := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := (Variety.pointsHomeomorph (heartIso G I w)).surjective x
    refine ⟨y, ?_⟩
    rw [← heartIso_hom_comp, Variety.mapPoints_comp]
    exact congrArg (Variety.mapPoints (heartInclusion G I w)) hy
  · rintro ⟨x, rfl⟩
    refine ⟨Variety.mapPoints (heartIso G I w).hom x, ?_⟩
    rw [← Variety.mapPoints_comp, heartIso_hom_comp]

/-- A flag lies in the heart exactly when it has the form v wB with v in Vd. -/
theorem mem_heart_iff (I : Set G.rootBase.support) (w : G.weylGroup)
    (q : (flagVariety G).points) :
    q ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) ↔
      ∃ v ∈ Vd.points G I w,
        flagVarietyPointsEquiv G (flagProjection G (v * G.weylPoint w)) = q := by
  rw [heartInclusion_points_range]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨rootSubsetPointsMulEquiv G _ (heartRootIndices_closed G I w) x, ?_, ?_⟩
    · rw [Vd.points_eq_rootSubset]
      exact (rootSubsetPointsMulEquiv G _ _ x).property
    · exact (heartRootMorphism_points G I w x).symm
  · rintro ⟨v, hv, rfl⟩
    rw [Vd.points_eq_rootSubset] at hv
    let x := (rootSubsetPointsMulEquiv G _ (heartRootIndices_closed G I w)).symm ⟨v, hv⟩
    refine ⟨x, ?_⟩
    rw [heartRootMorphism_points, show rootSubsetPointsMulEquiv G _ _ x = ⟨v, hv⟩ from
      MulEquiv.apply_symm_apply _ _]

end SchubertOrbits
