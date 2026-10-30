import OrbitComplexity.SchubertGeometry.FlagVariety.OverlapGraphs
import OrbitComplexity.GroupActions.Varieties.BorelPoints
import OrbitComplexity.GroupActions.Varieties.ClosedPoints
import OrbitComplexity.GroupActions.Varieties.Noetherian

/-!
# Closed overlap graphs in flag charts

Two rational chart coordinates represent the same flag precisely when their relative
group quotient lies in the Borel. Closed points determine constructible subsets, so the
graph of the coordinate transition is the inverse image of the closed Borel image.

## Main results

* `SchubertGeometry.flagOverlapGraph_range`: the graph image is the Borel incidence set.
* `SchubertGeometry.flagOverlapGraph_isClosed`: the overlap graph is a closed immersion.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory Topology TopologicalSpace

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem productPoints_ext (p q : (flagChartProduct G).points)
    (h₁ : GroupActions.Variety.mapPoints (flagChartFst G) p =
      GroupActions.Variety.mapPoints (flagChartFst G) q)
    (h₂ : GroupActions.Variety.mapPoints (flagChartSnd G) p =
      GroupActions.Variety.mapPoints (flagChartSnd G) q) : p = q := by
  apply (flagChartProduct G).pointsEquivOverHom.injective
  apply CartesianMonoidalCategory.hom_ext
  · exact congrArg (GroupActions.oppositeUnipotentVariety G).pointsEquivOverHom h₁
  · exact congrArg (GroupActions.oppositeUnipotentVariety G).pointsEquivOverHom h₂

private theorem graph_flag_iff (g h : G.points) (p : (flagChartProduct G).points) :
    p ∈ Set.range (GroupActions.Variety.mapPoints (flagOverlapGraph G g h)) ↔
      flagChartPoint G g (GroupActions.Variety.mapPoints (flagChartFst G) p) =
        flagChartPoint G h (GroupActions.Variety.mapPoints (flagChartSnd G) p) := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [← GroupActions.Variety.mapPoints_comp, flagOverlapGraph_fst,
      ← GroupActions.Variety.mapPoints_comp, flagOverlapGraph_snd,
      GroupActions.Variety.mapPoints_comp]
    exact (flagTransition_flag G g h x).symm
  · intro hp
    have hu : GroupActions.Variety.mapPoints (flagChartFst G) p ∈
        Set.range (GroupActions.Variety.mapPoints (flagOverlapInclusion G g h)) := by
      rw [GroupActions.Variety.range_mapPoints]
      change _ ∈ Set.range
        (((GroupActions.oppositeUnipotentVariety G).openInclusion (flagOverlap G g h)).left)
      rw [GroupActions.Variety.openInclusion_range]
      exact mem_flagOverlap_of_flag G g h _ _ hp
    obtain ⟨x, hx⟩ := hu
    refine ⟨x, productPoints_ext G _ _ ?_ ?_⟩
    · rw [← GroupActions.Variety.mapPoints_comp, flagOverlapGraph_fst]
      exact hx
    · apply flagChartPoint_injective G h
      rw [← GroupActions.Variety.mapPoints_comp, flagOverlapGraph_snd,
        GroupActions.Variety.mapPoints_comp, flagTransition_flag, hx]
      exact hp

omit [CharZero K] in
private theorem borelPoint_range (a : G.points) :
    GroupActions.reductivePointsEquiv G a ∈
        Set.range (GroupActions.Variety.mapPoints (GroupActions.borelInclusion G)) ↔
      a ∈ G.borelPoints := by
  constructor
  · rintro ⟨b, hb⟩
    rw [GroupActions.borelInclusion_points] at hb
    have he := (GroupActions.reductivePointsEquiv G).injective hb
    exact he ▸ (GroupActions.borelPointsMulEquiv G b).property
  · intro ha
    refine ⟨(GroupActions.borelPointsMulEquiv G).symm ⟨a, ha⟩, ?_⟩
    rw [GroupActions.borelInclusion_points,
      (GroupActions.borelPointsMulEquiv G).apply_symm_apply]

private theorem difference_flag_iff (g h : G.points) (p : (flagChartProduct G).points) :
    (flagChartProduct G).pointMap p ∈ (flagChartDifference G g h).left ⁻¹'
        Set.range (GroupActions.borelInclusion G).left ↔
      flagChartPoint G g (GroupActions.Variety.mapPoints (flagChartFst G) p) =
        flagChartPoint G h (GroupActions.Variety.mapPoints (flagChartSnd G) p) := by
  change (GroupActions.reductiveVariety G).pointMap
      (GroupActions.Variety.mapPoints (flagChartDifference G g h) p) ∈
        Set.range (GroupActions.borelInclusion G).left ↔ _
  change GroupActions.Variety.mapPoints (flagChartDifference G g h) p ∈
    (GroupActions.reductiveVariety G).pointMap ⁻¹'
      Set.range (GroupActions.borelInclusion G).left ↔ _
  rw [← GroupActions.Variety.range_mapPoints, flagChartDifference_points, borelPoint_range]
  exact (flagProjection_eq_iff G _ _).symm

private theorem closed_incidence (g h : G.points) :
    IsClosed ((flagChartDifference G g h).left ⁻¹'
      Set.range (GroupActions.borelInclusion G).left) :=
  (GroupActions.borelInclusion G).left.isClosedEmbedding.isClosed_range.preimage
    (flagChartDifference G g h).left.continuous

/-- The overlap graph is the inverse image of the Borel under the chart difference morphism. -/
theorem flagOverlapGraph_range (g h : G.points) :
    Set.range (flagOverlapGraph G g h).left =
      (flagChartDifference G g h).left ⁻¹' Set.range (GroupActions.borelInclusion G).left := by
  have : LocallyOfFiniteType (flagChartProduct G).toSpec :=
    (flagChartProduct G).locallyOfFiniteType
  have : IsNoetherian (flagChartProduct G).scheme :=
    GroupActions.Variety.noetherian (flagChartProduct G)
  have : NoetherianSpace (flagChartProduct G).toOver.left :=
    inferInstanceAs (NoetherianSpace (flagChartProduct G).scheme)
  have hS := GroupActions.Variety.isConstructible_range (flagOverlapGraph G g h)
  have hT : IsConstructible ((flagChartDifference G g h).left ⁻¹'
      Set.range (GroupActions.borelInclusion G).left) := by
    apply IsConstructible.of_compl
    apply IsRetrocompact.isConstructible (closed_incidence G g h).isOpen_compl
    intro U _ _
    exact NoetherianSpace.isCompact _
  have : JacobsonSpace (flagChartProduct G).scheme :=
    LocallyOfFiniteType.jacobsonSpace (flagChartProduct G).toSpec
  have : JacobsonSpace (flagChartProduct G).toOver.left :=
    inferInstanceAs (JacobsonSpace (flagChartProduct G).scheme)
  apply GroupActions.constructible_eq hS hT
  ext x
  by_cases hx : x ∈ closedPoints (flagChartProduct G).toOver.left
  · obtain ⟨p, hp⟩ := (flagChartProduct G).pointsEquivClosedPoints.surjective ⟨x, hx⟩
    have hp' : (flagChartProduct G).pointMap p = x := congrArg Subtype.val hp
    have hgraph : (flagChartProduct G).pointMap p ∈ Set.range (flagOverlapGraph G g h).left ↔
        p ∈ Set.range (GroupActions.Variety.mapPoints (flagOverlapGraph G g h)) := by
      rw [GroupActions.Variety.range_mapPoints]
      rfl
    simp only [Set.mem_inter_iff, hx, and_true]
    rw [← hp', hgraph, graph_flag_iff, difference_flag_iff]
  · simp only [Set.mem_inter_iff, hx, and_false]

/-- The graph of a flag-chart transition is a closed immersion into the product charts. -/
instance flagOverlapGraph_isClosed (g h : G.points) :
    IsClosedImmersion (flagOverlapGraph G g h).left := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [flagOverlapGraph_range]
  exact closed_incidence G g h

end
end SchubertGeometry
