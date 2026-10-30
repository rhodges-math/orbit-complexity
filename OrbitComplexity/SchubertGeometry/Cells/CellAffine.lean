import OrbitComplexity.SchubertGeometry.Cells.CellChart
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootIntersection
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.PresentationWordPropertyLength

/-! # Affine spaces underlying Schubert cells

The inversion subgroup is the intersection of the positive unipotent subgroup with the
Weyl-conjugated negative unipotent subgroup. Its flag image is the Schubert cell, whose
polynomial chart has one coordinate for each letter of a reduced Weyl expression.
-/

open CategoryTheory AlgebraicGeometry

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- A Schubert cell is affine space of dimension the Coxeter length of its Weyl element. -/
def schubertCellAffineIso (w : G.weylGroup) :
    (schubertCell G w).toOver ≅
      (GroupActions.affineVariety K
        (MvPolynomial
          (Fin ((ReductiveGroups.weylCoxeterSystem G.rootBase).length w)) K)).toOver := by
  rw [ReductiveGroups.weylCoxeterSystem_length G.rootBase w]
  exact (schubertCellChart G w).symm

/-- The scheme image of the inversion subgroup is exactly the Schubert cell. -/
theorem schubertCell_scheme_unipotent (w : G.weylGroup) :
    Set.range ((schubertCellInclusion G w).left : (schubertCell G w).scheme →
      (flagVariety G).scheme) =
    Set.range ((schubertRootMorphism G w).left : (schubertUnipotent G w).scheme →
      (flagVariety G).scheme) :=
  (GroupActions.Variety.range_eq_of_mapPoints _ _ (schubertRootMorphism_range G w)).symm

/-- Rational Schubert-cell points are the flags of inversion-group points times the Weyl element. -/
theorem schubertCell_points_unipotent (w : G.weylGroup) :
    Set.range (GroupActions.Variety.mapPoints (schubertCellInclusion G w)) =
      Set.range (fun u : schubertUnipotentPoints G w =>
        flagVarietyPointsEquiv G (flagProjection G ((u : G.points) * G.weylPoint w))) := by
  rw [← schubertRootMorphism_range G w]
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨schubertUnipotentPointsEquiv G w x,
      (schubertRootMorphism_points G w x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(schubertUnipotentPointsEquiv G w).symm x, ?_⟩
    rw [schubertRootMorphism_points]
    change flagVarietyPointsEquiv G (flagProjection G
      ((schubertUnipotentPointsEquiv G w
        ((schubertUnipotentPointsEquiv G w).symm x) : G.points) * G.weylPoint w)) = _
    rw [MulEquiv.apply_symm_apply]

end
end SchubertGeometry
