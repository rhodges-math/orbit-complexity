import OrbitComplexity.SchubertGeometry.Cells.SchubertPoints
import OrbitComplexity.GroupActions.Varieties.RootSubgroupPoints

/-! # Root coordinates for Schubert cells

The inversion-root subgroup is affine space and maps into the flag variety by its Weyl flag.
-/

open CategoryTheory AlgebraicGeometry

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The unipotent root subgroup indexed by the left inversions of a Weyl element. -/
abbrev schubertUnipotent (w : G.weylGroup) : GroupActions.Variety K :=
  GroupActions.rootSubsetVariety G (ReductiveGroups.leftRootInversionIndices G.rootBase w)
    (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)

/-- The closed inclusion of the Schubert unipotent subgroup into the reductive group. -/
abbrev schubertUnipotentInclusion (w : G.weylGroup) :
    (schubertUnipotent G w).toOver ⟶ (GroupActions.reductiveVariety G).toOver :=
  GroupActions.rootSubsetInclusion G _
    (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)

/-- Inversion-root coordinates identify the Schubert unipotent subgroup with affine space. -/
abbrev schubertUnipotentChart (w : G.weylGroup) :
    (GroupActions.affineSpaceVariety K
      {r : G.rootIndex // G.rootBase.IsPos r ∧
        r ∈ ReductiveGroups.leftRootInversionIndices G.rootBase w}).toOver ≅
      (schubertUnipotent G w).toOver :=
  GroupActions.rootSubsetChart G _
    (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)

/-- The Schubert unipotent subgroup has dimension the Weyl inversion count. -/
theorem schubertUnipotent_dim (w : G.weylGroup) :
    (schubertUnipotent G w).dim = ReductiveGroups.rootInversionCount G.rootBase w := by
  have hs : {r : G.rootIndex | G.rootBase.IsPos r ∧
      r ∈ ReductiveGroups.leftRootInversionIndices G.rootBase w} =
        ReductiveGroups.leftRootInversionIndices G.rootBase w := by
    ext r
    simp only [Set.mem_ofPred_eq, ReductiveGroups.mem_leftRootInversionIndices, and_self_left]
  have hc : Nat.card {r : G.rootIndex // G.rootBase.IsPos r ∧
      r ∈ ReductiveGroups.leftRootInversionIndices G.rootBase w} =
        ReductiveGroups.rootInversionCount G.rootBase w := by
    change {r : G.rootIndex | G.rootBase.IsPos r ∧
      r ∈ ReductiveGroups.leftRootInversionIndices G.rootBase w}.ncard = _
    rw [hs, ReductiveGroups.rootInversionCount, ReductiveGroups.leftRootInversions,
      Set.ncard_image_of_injective _ G.rootSystem.root.injective]
  rw [GroupActions.rootSubsetVariety_dim]
  exact congrArg (fun n : ℕ => (n : WithBot ℕ∞)) hc

/-- The inversion-root subgroup maps to flags by acting on its Weyl flag. -/
def schubertRootMorphism (w : G.weylGroup) :
    (schubertUnipotent G w).toOver ⟶ (flagVariety G).toOver :=
  schubertUnipotentInclusion G w ≫ GroupActions.Variety.orbitMorphism
    (GroupActions.reductiveVariety G) (flagVariety G) (weylFlagPoint G w)

/-- The inversion-root morphism sends a root point to its product with the Weyl representative. -/
theorem schubertRootMorphism_points (w : G.weylGroup) (x : (schubertUnipotent G w).points) :
    GroupActions.Variety.mapPoints (schubertRootMorphism G w) x =
      flagVarietyPointsEquiv G (flagProjection G
        ((GroupActions.rootSubsetPointsMulEquiv G _
          (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) x :
          G.points) * G.weylPoint w)) := by
  have hi : GroupActions.Variety.mapPoints (schubertUnipotentInclusion G w) x =
      GroupActions.reductivePointsMulEquiv G
        (GroupActions.rootSubsetPointsMulEquiv G _
          (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) x) :=
    GroupActions.rootSubsetInclusion_points G _ _ x
  exact (GroupActions.Variety.mapPoints_comp (schubertUnipotentInclusion G w)
    (GroupActions.Variety.orbitMorphism (GroupActions.reductiveVariety G)
      (flagVariety G) (weylFlagPoint G w)) x).trans
    ((GroupActions.Variety.mapPoints_orbitMorphism (GroupActions.reductiveVariety G)
      (flagVariety G) (weylFlagPoint G w) _).trans
      ((congrArg (fun h : (GroupActions.reductiveVariety G).points =>
        h • weylFlagPoint G w) hi).trans (flagVarietyAction_points G _ _)))

end
end SchubertGeometry
