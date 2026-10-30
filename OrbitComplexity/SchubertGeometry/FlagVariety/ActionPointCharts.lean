import OrbitComplexity.SchubertGeometry.FlagVariety.ActionCharts

/-! # Rational points of local action morphisms

Local multiplication gives the standard left action on rational Borel cosets.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K]

private theorem mapPoints_mul {X H : GroupActions.Variety K} [GrpObj H.toOver]
    (f g : X.toOver ⟶ H.toOver) (x : X.points) :
    GroupActions.Variety.mapPoints (f * g) x =
      GroupActions.Variety.mapPoints f x * GroupActions.Variety.mapPoints g x := by
  apply H.pointsEquivOverHom.injective
  rw [GroupActions.Variety.pointsEquivOverHom_mul]
  change X.pointsEquivOverHom x ≫ (f * g) =
    (X.pointsEquivOverHom x ≫ f) * (X.pointsEquivOverHom x ≫ g)
  exact MonObj.comp_mul _ _ _

variable [IsAlgClosed K] [CharZero K] (G : ReductiveGroups.ReductiveGroupData K)

private theorem quotientProduct_points
    (a b : (GroupActions.reductiveVariety G).points) :
    GroupActions.Variety.mapPoints (flagQuotientMorphism G) (a * b) =
      flagVarietyPointsEquiv G
        ((GroupActions.reductivePointsMulEquiv G).symm a •
          flagProjection G ((GroupActions.reductivePointsMulEquiv G).symm b)) := by
  obtain ⟨a, rfl⟩ := (GroupActions.reductivePointsMulEquiv G).surjective a
  obtain ⟨b, rfl⟩ := (GroupActions.reductivePointsMulEquiv G).surjective b
  rw [← map_mul]
  simp only [MulEquiv.symm_apply_apply]
  exact flagQuotientMorphism_points G (a * b)

/-- The local action has the usual left-action formula on unipotent chart points. -/
theorem flagActionChartMorphism_points (g : G.points)
    (p : (flagActionChartVariety G g).points) :
    GroupActions.Variety.mapPoints (flagActionChartMorphism G g) p =
      flagVarietyPointsEquiv G
        ((GroupActions.reductivePointsMulEquiv G).symm
          (GroupActions.Variety.mapPoints (flagActionChartFst G g ≫ flagActionFst G) p) •
            flagChartPoint G g (GroupActions.Variety.mapPoints (flagActionChartSnd G g) p)) := by
  simp only [flagActionChartMorphism, GroupActions.Variety.mapPoints_comp, mapPoints_mul,
    quotientProduct_points, GroupActions.Variety.mapPoints_comp, flagChartMap_points]
  change flagVarietyPointsEquiv G (_ • flagProjection G
    ((GroupActions.reductivePointsMulEquiv G).symm
      ((GroupActions.reductivePointsMulEquiv G) _))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The unipotent coordinate and ambient projection represent the same flag on an action chart. -/
theorem flagActionChart_flag (g : G.points) (p : (flagActionChartVariety G g).points) :
    flagVarietyPointsEquiv G
      (flagChartPoint G g (GroupActions.Variety.mapPoints (flagActionChartSnd G g) p)) =
        GroupActions.Variety.mapPoints (flagActionChartFst G g ≫ flagActionSnd G) p := by
  have he := congrArg (fun f => GroupActions.Variety.mapPoints f p)
    (flagActionChart_condition G g)
  simpa only [GroupActions.Variety.mapPoints_comp, flagChartMorphism_points] using he

end
end SchubertGeometry