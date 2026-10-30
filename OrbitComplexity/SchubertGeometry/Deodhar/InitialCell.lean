import OrbitComplexity.SchubertGeometry.Cells.CellChart
import Mathlib.Algebra.MvPolynomial.Equiv


/-! # The initial Schubert cell

The identity cell is the spectrum of the base field. Its flag is the identity Borel coset.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev initialRoots :=
  {r : G.rootIndex // G.rootBase.IsPos r ∧
    r ∈ leftRootInversionIndices G.rootBase (1 : G.weylGroup)}

private instance initialRoots_empty : IsEmpty (initialRoots G) where
  false r := by
    obtain ⟨r, hr⟩ := r
    simpa only [leftRootInversionIndices_one, Set.mem_empty_iff_false] using hr.2

/-- The identity cell has no root coordinates and is the spectrum of the base field. -/
def initialCellIso : (GroupActions.affineVariety K K).toOver ≅ (schubertCell G 1).toOver :=
  (algSpec (CommRingCat.of K)).mapIso
    (CommAlgCat.isoMk (MvPolynomial.isEmptyAlgEquiv K (initialRoots G))).op ≪≫
    GroupActions.rootSubsetChart G (leftRootInversionIndices G.rootBase 1)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase 1) ≪≫ schubertCellIso G 1

/-- Every rational point of the initial cell maps to the identity flag. -/
theorem initialCellIso_points (p : (GroupActions.affineVariety K K).points) :
    GroupActions.Variety.mapPoints
      ((initialCellIso G).hom ≫ schubertCellInclusion G 1) p =
      flagVarietyPointsEquiv G (flagProjection G 1) := by
  have hp : GroupActions.Variety.mapPoints
      ((initialCellIso G).hom ≫ schubertCellInclusion G 1) p ∈
      Set.range (GroupActions.Variety.mapPoints (schubertCellInclusion G 1)) := by
    rw [GroupActions.Variety.mapPoints_comp]
    exact ⟨_, rfl⟩
  rw [schubertCell_points_range] at hp
  obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hp
  have hw : G.weylPoint 1 = 1 := by rw [G.weylPoint_eq, weylElementPoint_one]
  have hflag : flagProjection G (GroupActions.borelPointsMulEquiv G b : G.points) =
      flagProjection G 1 := by
    apply Eq.symm
    apply (flagProjection_eq_iff G _ _).mpr
    simpa only [inv_one, one_mul] using (GroupActions.borelPointsMulEquiv G b).property
  have hpoint : b • weylFlagPoint G 1 = flagVarietyPointsEquiv G (flagProjection G 1) := by
    rw [weylFlagPoint, borelFlag_smul, hw]
    change flagVarietyPointsEquiv G (flagProjection G
      ((GroupActions.borelPointsMulEquiv G b : G.points) * 1)) = _
    rw [mul_one, hflag]
  exact hb.symm.trans hpoint

end
end SchubertGeometry
