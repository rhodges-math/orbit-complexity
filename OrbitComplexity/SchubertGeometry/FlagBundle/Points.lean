import OrbitComplexity.SchubertGeometry.FlagBundle.Maps
import OrbitComplexity.SchubertGeometry.Cells.Actions
/-! # Rational points of associated flag bundles

A chart centred at a group representative lifts every fibre point. Its projection
and equivariant endpoint agree with the corresponding flag and group action.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) (Y : GroupActions.Variety K)
  [ModObj (GroupActions.borelVariety G).toOver Y.toOver]

/-- The bundle point represented by a group point and a fibre point. -/
def flagBundlePoint (g : G.points) (y : Y.points) :
    Spec (CommRingCat.of K) ⟶ flagBundleScheme G Y :=
  (lift ((GroupActions.oppositeUnipotentVariety G).pointsEquivOverHom 1)
    (Y.pointsEquivOverHom y)).left ≫ flagBundleChart G Y g

/-- The projection of a represented bundle point is its group representative modulo the Borel. -/
theorem flagBundlePoint_projection (g : G.points) (y : Y.points) :
    flagBundlePoint G Y g y ≫ flagBundleProjection G Y =
      (flagVarietyPointsEquiv G (flagProjection G g)).val := by
  unfold flagBundlePoint
  rw [Category.assoc, flagBundleChart_projection]
  change (lift ((GroupActions.oppositeUnipotentVariety G).pointsEquivOverHom 1)
    (Y.pointsEquivOverHom y) ≫
      fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫
        flagChartMorphism G g).left = _
  rw [lift_fst_assoc]
  have hc : flagChartPoint G g 1 = flagProjection G g := by
    simp only [flagChartPoint, map_one, OneMemClass.coe_one, mul_one]
  have hq := flagChartMorphism_points G g 1
  rw [hc] at hq
  exact congrArg Subtype.val hq

/-- A represented bundle point lies over the identity point of the coefficient field. -/
theorem flagBundlePoint_toSpec (g : G.points) (y : Y.points) :
    flagBundlePoint G Y g y ≫ flagBundleProjection G Y ≫ (flagVariety G).toSpec = 𝟙 _ := by
  rw [← Category.assoc, flagBundlePoint_projection]
  exact (flagVarietyPointsEquiv G (flagProjection G g)).property

variable (j : Y.toOver ⟶ (flagVariety G).toOver)
  [IsModHom (GroupActions.borelVariety G).toOver j]

/-- An equivariant bundle endpoint sends a represented point to the group translate of its fibre. -/
theorem flagBundlePoint_map (g : G.points) (y : Y.points) :
    flagBundlePoint G Y g y ≫ flagBundleMap G Y j =
      (GroupActions.reductivePointsMulEquiv G g • GroupActions.Variety.mapPoints j y).val := by
  unfold flagBundlePoint
  rw [Category.assoc, flagBundleChart_map]
  change (lift ((GroupActions.oppositeUnipotentVariety G).pointsEquivOverHom 1)
    (Y.pointsEquivOverHom y) ≫
      ((fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫ flagChartMap G g) •
        (snd (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫ j))).left = _
  rw [ModObj.comp_smul, lift_fst_assoc, lift_snd_assoc]
  have hg : GroupActions.Variety.mapPoints (flagChartMap G g) 1 =
      GroupActions.reductivePointsMulEquiv G g := by
    rw [flagChartMap_points]
    simp only [map_one, OneMemClass.coe_one, mul_one]
    rfl
  change ((GroupActions.reductiveVariety G).pointsEquivOverHom
      (GroupActions.Variety.mapPoints (flagChartMap G g) 1) •
        (flagVariety G).pointsEquivOverHom (GroupActions.Variety.mapPoints j y)).left = _
  rw [hg]
  exact (congrArg Over.Hom.left
    (GroupActions.Variety.pointsEquivOverHom_smul
      (GroupActions.reductiveVariety G) (flagVariety G)
      (GroupActions.reductivePointsMulEquiv G g) (GroupActions.Variety.mapPoints j y))).symm

end SchubertGeometry
