import OrbitComplexity.SchubertGeometry.FlagVariety.PointTopology

/-! # Open affine charts of the flag variety

Translated opposite-unipotent coordinates give open variety morphisms and rational charts.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- A translated opposite-unipotent chart is a morphism into the flag variety. -/
def flagChartMorphism (g : G.points) :
    (GroupActions.oppositeUnipotentVariety G).toOver ⟶ (flagVariety G).toOver :=
  Over.homMk (flagSchemeChart G g) (flagSchemeChart_toSpec G g)

/-- Each translated unipotent chart is an open immersion of varieties. -/
instance flagChartMorphism_isOpen (g : G.points) :
    IsOpenImmersion (flagChartMorphism G g).left := flagSchemeChart_isOpen G g

/-- Rational points of the variety chart are the corresponding Borel cosets. -/
theorem flagChartMorphism_points (g : G.points)
    (u : (GroupActions.oppositeUnipotentVariety G).points) :
    GroupActions.Variety.mapPoints (flagChartMorphism G g) u =
      flagVarietyPointsEquiv G (flagChartPoint G g u) :=
  (flagSchemePointsEquiv_chart G g u).symm

/-- The unipotent chart on Borel cosets is an open embedding for the quotient topology. -/
theorem flagChartPoint_isOpen (g : G.points) : IsOpenEmbedding (flagChartPoint G g) := by
  have he : flagChartPoint G g = (flagVarietyPointsHomeomorph G).symm ∘
      GroupActions.Variety.mapPoints (flagChartMorphism G g) := by
    funext u
    exact ((flagVarietyPointsHomeomorph G).symm_apply_apply (flagChartPoint G g u)).symm.trans
      (congrArg (flagVarietyPointsHomeomorph G).symm (flagChartMorphism_points G g u).symm)
  rw [he]
  exact (flagVarietyPointsHomeomorph G).symm.isOpenEmbedding.comp
    (GroupActions.Variety.isOpenEmbedding_mapPoints (flagChartMorphism G g))

end
end SchubertGeometry