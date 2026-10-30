import OrbitComplexity.SchubertGeometry.FlagVariety.Transitions
import OrbitComplexity.GroupActions.Rosenlicht.ProductSections
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Graphs and differences of flag chart coordinates

Each chart transition has a graph in the product of the two unipotent charts. Its first
projection is an open immersion, which makes the graph a preimmersion. The relative
quotient of the two translated group coordinates is an algebraic morphism on that product.

## Main definitions

* `SchubertGeometry.flagOverlapGraph`: the graph of a chart transition.
* `SchubertGeometry.flagChartDifference`: the quotient of the two group coordinates.

## Main results

* `SchubertGeometry.flagOverlapGraph_preimmersion`: the graph is a preimmersion.
* `SchubertGeometry.flagChartDifference_points`: its relative quotient on rational points.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory Topology

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

private theorem mapPoints_inv {X H : GroupActions.Variety K} [GrpObj H.toOver]
    (f : X.toOver ⟶ H.toOver) (x : X.points) :
    GroupActions.Variety.mapPoints f⁻¹ x = (GroupActions.Variety.mapPoints f x)⁻¹ := by
  apply H.pointsEquivOverHom.injective
  rw [GroupActions.Variety.pointsEquivOverHom_inv]
  change X.pointsEquivOverHom x ≫ f⁻¹ = (X.pointsEquivOverHom x ≫ f)⁻¹
  exact GrpObj.comp_inv _ _

variable [IsAlgClosed K] [CharZero K] (G : ReductiveGroups.ReductiveGroupData K)

/-- The product of two opposite unipotent charts over the base field. -/
abbrev flagChartProduct : GroupActions.Variety K :=
  GroupActions.Variety.productVariety
    (GroupActions.oppositeUnipotentVariety G) (GroupActions.oppositeUnipotentVariety G)

/-- The first projection from a product of opposite unipotent charts. -/
def flagChartFst : (flagChartProduct G).toOver ⟶
    (GroupActions.oppositeUnipotentVariety G).toOver := fst _ _

/-- The second projection from a product of opposite unipotent charts. -/
def flagChartSnd : (flagChartProduct G).toOver ⟶
    (GroupActions.oppositeUnipotentVariety G).toOver := snd _ _

/-- The graph of the coordinate change on the overlap of two flag charts. -/
def flagOverlapGraph (g h : G.points) :
    (flagOverlapVariety G g h).toOver ⟶ (flagChartProduct G).toOver :=
  lift (flagOverlapInclusion G g h) (flagTransition G g h ≫ flagOverlapInclusion G h g)

/-- The first graph coordinate is the overlap inclusion. -/
theorem flagOverlapGraph_fst (g h : G.points) :
    flagOverlapGraph G g h ≫ flagChartFst G = flagOverlapInclusion G g h :=
  lift_fst _ _

/-- The second graph coordinate is the transition followed by the reverse inclusion. -/
theorem flagOverlapGraph_snd (g h : G.points) :
    flagOverlapGraph G g h ≫ flagChartSnd G =
      flagTransition G g h ≫ flagOverlapInclusion G h g := lift_snd _ _

/-- Overlap graphs are embeddings with surjective maps on stalks. -/
instance flagOverlapGraph_preimmersion (g h : G.points) :
    IsPreimmersion (flagOverlapGraph G g h).left := by
  have hc : (flagOverlapGraph G g h).left ≫ (flagChartFst G).left =
      (flagOverlapInclusion G g h).left :=
    congrArg Over.Hom.left (flagOverlapGraph_fst G g h)
  have : IsPreimmersion ((flagOverlapGraph G g h).left ≫ (flagChartFst G).left) := by
    rw [hc]
    infer_instance
  refine { stalkMap_surjective := ?_, isEmbedding := ?_ }
  · intro x
    have hs := ((flagOverlapGraph G g h).left ≫ (flagChartFst G).left).stalkMap_surjective x
    rw [Scheme.Hom.stalkMap_comp] at hs
    exact Function.Surjective.of_comp hs
  · apply IsEmbedding.of_comp (flagOverlapGraph G g h).left.continuous
      (flagChartFst G).left.continuous
    change IsEmbedding ((flagOverlapGraph G g h).left ≫ (flagChartFst G).left)
    rw [hc]
    exact (flagOverlapInclusion G g h).left.isEmbedding

/-- The relative group point of a pair of translated chart coordinates. -/
def flagChartDifference (g h : G.points) :
    (flagChartProduct G).toOver ⟶ (GroupActions.reductiveVariety G).toOver :=
  (flagChartFst G ≫ flagChartMap G g)⁻¹ * (flagChartSnd G ≫ flagChartMap G h)

/-- On rational chart pairs, the difference morphism is the quotient of group representatives. -/
theorem flagChartDifference_points (g h : G.points) (p : (flagChartProduct G).points) :
    GroupActions.Variety.mapPoints (flagChartDifference G g h) p =
      GroupActions.reductivePointsEquiv G
        ((g * (GroupActions.oppositeUnipotentPointsMulEquiv G
          (GroupActions.Variety.mapPoints (flagChartFst G) p) : G.points))⁻¹ *
        (h * (GroupActions.oppositeUnipotentPointsMulEquiv G
          (GroupActions.Variety.mapPoints (flagChartSnd G) p) : G.points))) := by
  rw [flagChartDifference, mapPoints_mul, mapPoints_inv,
    GroupActions.Variety.mapPoints_comp, GroupActions.Variety.mapPoints_comp,
    flagChartMap_points, flagChartMap_points]
  change ((GroupActions.reductivePointsMulEquiv G) _)⁻¹ *
      (GroupActions.reductivePointsMulEquiv G) _ =
    (GroupActions.reductivePointsMulEquiv G) (_⁻¹ * _)
  simp only [map_mul, map_inv]

end
end SchubertGeometry
