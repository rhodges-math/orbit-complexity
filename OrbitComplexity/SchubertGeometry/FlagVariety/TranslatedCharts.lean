import OrbitComplexity.SchubertGeometry.FlagVariety.BigCellPoints
import OrbitComplexity.GroupActions.Actions.Translations
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties
import OrbitComplexity.GroupActions.Varieties.OpenPointLifts

/-!
# Translated opposite unipotent charts

A translate of the opposite unipotent subgroup maps to the reductive group. The relative
chart map detects an open overlap by its inverse image of the big cell. On that overlap,
the big-cell inverse supplies the new unipotent coordinate and a Borel coordinate.

## Main definitions

* `SchubertGeometry.flagChartMap`: a translated opposite unipotent chart.
* `SchubertGeometry.flagOverlap`: the open overlap of two charts.
* `SchubertGeometry.flagOverlapCoordinate`: the coordinate in the second chart.

## Main results

* `SchubertGeometry.flagOverlap_factor`: factorization of relative coordinates.
-/

open CategoryTheory AlgebraicGeometry

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- A translated opposite unipotent chart maps into the reductive group. -/
def flagChartMap (g : G.points) :
    (GroupActions.oppositeUnipotentVariety G).toOver ⟶
      (GroupActions.reductiveVariety G).toOver :=
  GroupActions.oppositeUnipotentInclusion G ≫
    (GroupActions.leftTranslation (GroupActions.reductiveVariety G)
      (GroupActions.reductivePointsMulEquiv G g)).hom

/-- The chart map on rational points is left multiplication by its chart index. -/
theorem flagChartMap_points (g : G.points)
    (x : (GroupActions.oppositeUnipotentVariety G).points) :
    GroupActions.Variety.mapPoints (flagChartMap G g) x =
      GroupActions.reductivePointsEquiv G
        (g * (GroupActions.oppositeUnipotentPointsMulEquiv G x : G.points)) := by
  rw [flagChartMap, GroupActions.Variety.mapPoints_comp,
    GroupActions.leftTranslation_points, GroupActions.oppositeUnipotentInclusion_points]
  exact ((GroupActions.reductivePointsMulEquiv G).map_mul _ _).symm

/-- The overlap of two charts is the inverse image of the big cell under their relative map. -/
def flagOverlap (g h : G.points) : (GroupActions.oppositeUnipotentVariety G).scheme.Opens :=
  (flagChartMap G (h⁻¹ * g)).left ⁻¹ᵁ (bigCellMorphism G).left.opensRange

/-- The open variety on the overlap of two translated charts. -/
def flagOverlapVariety (g h : G.points) : GroupActions.Variety K :=
  (GroupActions.oppositeUnipotentVariety G).openSubvariety (flagOverlap G g h)

/-- The inclusion of an overlap in its first opposite unipotent chart. -/
def flagOverlapInclusion (g h : G.points) : (flagOverlapVariety G g h).toOver ⟶
    (GroupActions.oppositeUnipotentVariety G).toOver :=
  (GroupActions.oppositeUnipotentVariety G).openInclusion (flagOverlap G g h)

/-- Overlap inclusions are open immersions. -/
instance flagOverlapInclusion_isOpen (g h : G.points) :
    IsOpenImmersion (flagOverlapInclusion G g h).left := by
  exact GroupActions.Variety.openInclusion_isOpenImmersion _ _

/-- Overlap membership means that the relative chart image lies in the big cell. -/
theorem mem_flagOverlap_iff (g h : G.points)
    (x : (GroupActions.oppositeUnipotentVariety G).points) :
    (GroupActions.oppositeUnipotentVariety G).pointMap x ∈ flagOverlap G g h ↔
      GroupActions.Variety.mapPoints (flagChartMap G (h⁻¹ * g)) x ∈
        Set.range (GroupActions.Variety.mapPoints (bigCellMorphism G)) := by
  rw [GroupActions.Variety.range_mapPoints]
  rfl

private theorem overlap_image (g h : G.points)
    (x : (flagOverlapVariety G g h).points) :
    GroupActions.Variety.mapPoints
        (flagOverlapInclusion G g h ≫ flagChartMap G (h⁻¹ * g)) x ∈
      Set.range (GroupActions.Variety.mapPoints (bigCellMorphism G)) := by
  rw [GroupActions.Variety.mapPoints_comp, ← mem_flagOverlap_iff]
  exact ((flagOverlapVariety G g h).pointMap x).property

/-- The relative chart map on an overlap factors through the affine big cell. -/
def flagOverlapProduct (g h : G.points) :
    (flagOverlapVariety G g h).toOver ⟶ (bigCellVariety G).toOver :=
  GroupActions.Variety.liftOpen
    (flagOverlapInclusion G g h ≫ flagChartMap G (h⁻¹ * g))
    (bigCellMorphism G) (overlap_image G g h)

/-- The lifted product recovers the relative chart map after multiplication. -/
theorem flagOverlapProduct_comp (g h : G.points) :
    flagOverlapProduct G g h ≫ bigCellMorphism G =
      flagOverlapInclusion G g h ≫ flagChartMap G (h⁻¹ * g) :=
  GroupActions.Variety.liftOpen_comp _ _ _

/-- The first coordinate of the overlap product is the coordinate in the second chart. -/
def flagOverlapCoordinate (g h : G.points) :
    (flagOverlapVariety G g h).toOver ⟶
      (GroupActions.oppositeUnipotentVariety G).toOver :=
  flagOverlapProduct G g h ≫ bigCellFst G

/-- The Borel coordinate of the relative product on a chart overlap. -/
def flagOverlapBorel (g h : G.points) :
    (flagOverlapVariety G g h).toOver ⟶ (GroupActions.borelVariety G).toOver :=
  flagOverlapProduct G g h ≫ bigCellSnd G

/-- Relative group coordinates factor as the new unipotent coordinate times a Borel point. -/
theorem flagOverlap_factor (g h : G.points) (x : (flagOverlapVariety G g h).points) :
    (h⁻¹ * g) * (GroupActions.oppositeUnipotentPointsMulEquiv G
      (GroupActions.Variety.mapPoints (flagOverlapInclusion G g h) x) : G.points) =
      (GroupActions.oppositeUnipotentPointsMulEquiv G
        (GroupActions.Variety.mapPoints (flagOverlapCoordinate G g h) x) : G.points) *
      (GroupActions.borelPointsMulEquiv G
        (GroupActions.Variety.mapPoints (flagOverlapBorel G g h) x) : G.points) := by
  have he := congrArg (fun f => GroupActions.Variety.mapPoints f x)
    (flagOverlapProduct_comp G g h)
  rw [GroupActions.Variety.mapPoints_comp, GroupActions.Variety.mapPoints_comp,
    bigCellMorphism_points, flagChartMap_points] at he
  apply (GroupActions.reductivePointsEquiv G).injective
  rw [← he]
  congr 2
  · rw [flagOverlapCoordinate, GroupActions.Variety.mapPoints_comp,
      ← bigCellPointsEquiv_fst]
  · rw [flagOverlapBorel, GroupActions.Variety.mapPoints_comp,
      ← bigCellPointsEquiv_snd]

end
end SchubertGeometry
