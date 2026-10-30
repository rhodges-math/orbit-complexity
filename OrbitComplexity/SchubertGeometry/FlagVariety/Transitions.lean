import OrbitComplexity.SchubertGeometry.FlagVariety.TranslatedCharts
import OrbitComplexity.SchubertGeometry.FlagVariety.Charts

/-!
# Changes of opposite unipotent chart coordinates

The relative big-cell factorization maps each overlap into the reverse overlap. These
morphisms preserve rational flags, so injectivity of unipotent flag coordinates proves
that the two transitions are inverse and that self-transitions are identities.

## Main definitions

* `SchubertGeometry.flagChartPoint`: a rational flag in a translated chart.
* `SchubertGeometry.flagTransition`: the change of coordinates between two chart overlaps.

## Main results

* `SchubertGeometry.flagTransition_inv`: opposite transitions are inverse.
* `SchubertGeometry.flagOverlap_self`: the self-overlap is the whole chart.
-/

open CategoryTheory AlgebraicGeometry

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The rational flag represented by a point in a translated opposite unipotent chart. -/
def flagChartPoint (g : G.points) (x : (GroupActions.oppositeUnipotentVariety G).points) :
    flagPoints G :=
  flagProjection G (g * (GroupActions.oppositeUnipotentPointsMulEquiv G x : G.points))

/-- A translated opposite unipotent chart is injective on rational flag points. -/
theorem flagChartPoint_injective (g : G.points) :
    Function.Injective (flagChartPoint G g) := by
  intro x y hxy
  apply (GroupActions.oppositeUnipotentPointsMulEquiv G).injective
  apply flagProjection_injective G G.oppositeUnipotentPoints
    (disjoint_iff.mp G.oppositeUnipotentPoints_disjoint)
  exact MulAction.injective g (by
    simpa only [flagChartPoint, flagProjection_smul] using hxy)

/-- The two chart coordinates on an overlap represent the same rational flag. -/
theorem flagOverlapCoordinate_flag (g h : G.points) (x : (flagOverlapVariety G g h).points) :
    flagChartPoint G g (GroupActions.Variety.mapPoints (flagOverlapInclusion G g h) x) =
      flagChartPoint G h (GroupActions.Variety.mapPoints (flagOverlapCoordinate G g h) x) := by
  let u : G.oppositeUnipotentPoints := GroupActions.oppositeUnipotentPointsMulEquiv G
    (GroupActions.Variety.mapPoints (flagOverlapInclusion G g h) x)
  let v : G.oppositeUnipotentPoints := GroupActions.oppositeUnipotentPointsMulEquiv G
    (GroupActions.Variety.mapPoints (flagOverlapCoordinate G g h) x)
  let b : G.borelPoints := GroupActions.borelPointsMulEquiv G
    (GroupActions.Variety.mapPoints (flagOverlapBorel G g h) x)
  have he : (h⁻¹ * g) * u = v * b := flagOverlap_factor G g h x
  change flagProjection G (g * u) = flagProjection G (h * v)
  have hgu : g * u = h * (v * b) := by
    calc
      g * u = h * ((h⁻¹ * g) * u) := by group
      _ = h * (v * b) := by rw [he]
  rw [hgu, flagProjection_eq_iff]
  have hb : (h * (v * b))⁻¹ * (h * v) = (b : G.points)⁻¹ := by group
  rw [hb]
  exact G.borelPoints.inv_mem b.property

private theorem overlapCoordinate_mem (g h : G.points)
    (x : (flagOverlapVariety G g h).points) :
    (GroupActions.oppositeUnipotentVariety G).pointMap
      (GroupActions.Variety.mapPoints (flagOverlapCoordinate G g h) x) ∈ flagOverlap G h g := by
  rw [mem_flagOverlap_iff]
  let u := GroupActions.Variety.mapPoints (flagOverlapInclusion G g h) x
  let v := GroupActions.Variety.mapPoints (flagOverlapCoordinate G g h) x
  let b := GroupActions.Variety.mapPoints (flagOverlapBorel G g h) x
  refine ⟨(bigCellPointsEquiv G).symm (u, b⁻¹), ?_⟩
  rw [bigCellMorphism_points, Equiv.apply_symm_apply, flagChartMap_points]
  apply congrArg (GroupActions.reductivePointsEquiv G)
  change (GroupActions.oppositeUnipotentPointsMulEquiv G u : G.points) *
      (GroupActions.borelPointsMulEquiv G b⁻¹ : G.points) =
    (g⁻¹ * h) * (GroupActions.oppositeUnipotentPointsMulEquiv G v : G.points)
  rw [map_inv]
  change (GroupActions.oppositeUnipotentPointsMulEquiv G u : G.points) *
      (GroupActions.borelPointsMulEquiv G b : G.points)⁻¹ = _
  have he := flagOverlap_factor G g h x
  calc
    _ = g⁻¹ * h * ((h⁻¹ * g) *
        (GroupActions.oppositeUnipotentPointsMulEquiv G u : G.points)) *
        (GroupActions.borelPointsMulEquiv G b : G.points)⁻¹ := by group
    _ = g⁻¹ * h *
        ((GroupActions.oppositeUnipotentPointsMulEquiv G v : G.points) *
          (GroupActions.borelPointsMulEquiv G b : G.points)) *
        (GroupActions.borelPointsMulEquiv G b : G.points)⁻¹ := by rw [he]
    _ = _ := by group

private theorem overlapCoordinate_image (g h : G.points)
    (x : (flagOverlapVariety G g h).points) :
    GroupActions.Variety.mapPoints (flagOverlapCoordinate G g h) x ∈
      Set.range (GroupActions.Variety.mapPoints (flagOverlapInclusion G h g)) := by
  rw [GroupActions.Variety.range_mapPoints]
  change _ ∈ Set.range
    (((GroupActions.oppositeUnipotentVariety G).openInclusion (flagOverlap G h g)).left)
  rw [GroupActions.Variety.openInclusion_range]
  exact overlapCoordinate_mem G g h x

/-- The change of opposite unipotent coordinates between two chart overlaps. -/
def flagTransition (g h : G.points) :
    (flagOverlapVariety G g h).toOver ⟶ (flagOverlapVariety G h g).toOver :=
  GroupActions.Variety.liftOpen (flagOverlapCoordinate G g h)
    (flagOverlapInclusion G h g) (overlapCoordinate_image G g h)

/-- The transition followed by overlap inclusion is the second chart coordinate. -/
theorem flagTransition_comp (g h : G.points) :
    flagTransition G g h ≫ flagOverlapInclusion G h g = flagOverlapCoordinate G g h :=
  GroupActions.Variety.liftOpen_comp _ _ _

/-- A coordinate transition preserves the represented rational flag. -/
theorem flagTransition_flag (g h : G.points) (x : (flagOverlapVariety G g h).points) :
    flagChartPoint G h (GroupActions.Variety.mapPoints (flagOverlapInclusion G h g)
      (GroupActions.Variety.mapPoints (flagTransition G g h) x)) =
      flagChartPoint G g (GroupActions.Variety.mapPoints (flagOverlapInclusion G g h) x) := by
  rw [← GroupActions.Variety.mapPoints_comp, flagTransition_comp]
  exact (flagOverlapCoordinate_flag G g h x).symm

/-- Reversing a chart transition gives its inverse. -/
theorem flagTransition_inv (g h : G.points) :
    flagTransition G g h ≫ flagTransition G h g = 𝟙 _ := by
  apply GroupActions.Variety.mapPoints_injective
  funext x
  apply GroupActions.Variety.mapPoints_injective_of_mono (flagOverlapInclusion G g h)
  apply flagChartPoint_injective G g
  simp only [GroupActions.Variety.mapPoints_comp, GroupActions.Variety.mapPoints_id,
    flagTransition_flag]

/-- A transition from a chart to itself is the identity. -/
theorem flagTransition_self (g : G.points) : flagTransition G g g = 𝟙 _ := by
  apply GroupActions.Variety.mapPoints_injective
  funext x
  apply GroupActions.Variety.mapPoints_injective_of_mono (flagOverlapInclusion G g g)
  apply flagChartPoint_injective G g
  rw [GroupActions.Variety.mapPoints_id, flagTransition_flag]

/-- A chart overlaps with itself on its entire domain. -/
theorem flagOverlap_self (g : G.points) : flagOverlap G g g = ⊤ := by
  apply top_unique
  have H := GroupActions.Variety.range_subset_open_of_points
    (𝟙 (GroupActions.oppositeUnipotentVariety G).toOver) (flagOverlap G g g) (fun u => by
      rw [GroupActions.Variety.mapPoints_id, mem_flagOverlap_iff]
      refine ⟨(bigCellPointsEquiv G).symm (u, 1), ?_⟩
      rw [bigCellMorphism_points, Equiv.apply_symm_apply, flagChartMap_points]
      apply congrArg (GroupActions.reductivePointsEquiv G)
      simp only [map_one, OneMemClass.coe_one, mul_one, inv_mul_cancel, one_mul])
  intro x _
  exact H ⟨x, rfl⟩

/-- The overlap inclusion for a chart with itself is an isomorphism. -/
instance flagOverlapInclusion_self (g : G.points) :
    IsIso (flagOverlapInclusion G g g).left := by
  change IsIso (flagOverlap G g g).ι
  rw [flagOverlap_self]
  exact (Scheme.topIso _).isIso_hom

/-- Equal rational flags give membership in the relative chart overlap. -/
theorem mem_flagOverlap_of_flag (g h : G.points)
    (u v : (GroupActions.oppositeUnipotentVariety G).points)
    (he : flagChartPoint G g u = flagChartPoint G h v) :
    (GroupActions.oppositeUnipotentVariety G).pointMap u ∈ flagOverlap G g h := by
  let a : G.oppositeUnipotentPoints := GroupActions.oppositeUnipotentPointsMulEquiv G u
  let c : G.oppositeUnipotentPoints := GroupActions.oppositeUnipotentPointsMulEquiv G v
  have hb : (g * a)⁻¹ * (h * c) ∈ G.borelPoints := (flagProjection_eq_iff G _ _).mp he
  let b : G.borelPoints := ⟨(g * a)⁻¹ * (h * c), hb⟩
  rw [mem_flagOverlap_iff]
  refine ⟨(bigCellPointsEquiv G).symm
    (v, (GroupActions.borelPointsMulEquiv G).symm b⁻¹), ?_⟩
  rw [bigCellMorphism_points, Equiv.apply_symm_apply, flagChartMap_points]
  apply congrArg (GroupActions.reductivePointsEquiv G)
  rw [(GroupActions.borelPointsMulEquiv G).apply_symm_apply]
  change (c : G.points) * (b : G.points)⁻¹ = (h⁻¹ * g) * a
  change (c : G.points) * ((g * a)⁻¹ * (h * c))⁻¹ = (h⁻¹ * g) * a
  group

end
end SchubertGeometry
