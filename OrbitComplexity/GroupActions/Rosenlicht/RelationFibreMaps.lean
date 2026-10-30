import OrbitComplexity.GroupActions.Rosenlicht.ProductFibres
import OrbitComplexity.GroupActions.Rosenlicht.RelationVarieties

/-!
# Orbit relation fibres inside the variety

The second coordinate embeds a relation fibre over a rational point as a closed
subset of the original variety. The construction uses the product-fibre
identifications and preserves Krull dimension.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory Topology

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

private def relationFibreLift (x : X.points) :
    ((orbitRelationProjection H X).left ⁻¹' {X.pointMap x}) →
      ((fst X.toOver X.toOver).left ⁻¹' {X.pointMap x}) :=
  fun z ↦ ⟨(orbitRelationInclusion H X).left z.val, z.property⟩

private lemma relationFibreLift_closed (x : X.points) :
    IsClosedEmbedding (relationFibreLift H X x) := by
  have hx : IsClosed ({X.pointMap x} : Set X.scheme) :=
    (X.pointsEquivClosedPoints x).property
  have hs : IsClosedEmbedding
      (Subtype.val : ((orbitRelationProjection H X).left ⁻¹' {X.pointMap x}) →
        (orbitRelationVariety H X).scheme) :=
    (hx.preimage (orbitRelationProjection H X).left.continuous).isClosedEmbedding_subtypeVal
  have hi := (orbitRelationInclusion H X).left.isClosedEmbedding.comp hs
  let T := (fst X.toOver X.toOver).left ⁻¹' {X.pointMap x}
  have hm : ∀ z, (orbitRelationInclusion H X).left (z :
      (orbitRelationProjection H X).left ⁻¹' {X.pointMap x}).val ∈ T :=
    fun z ↦ (relationFibreLift H X x z).property
  change IsClosedEmbedding
    (T.codRestrict (fun (z : (orbitRelationProjection H X).left ⁻¹' {X.pointMap x}) ↦
      (orbitRelationInclusion H X).left z.val) hm)
  exact IsClosedEmbedding.of_isEmbedding_isClosedMap
    (hi.isEmbedding.codRestrict T hm) (hi.isClosedMap.codRestrict hm)

/-- The second coordinate maps an orbit relation fibre into the original variety. -/
def relationFibreMap (x : X.points)
    (z : (orbitRelationProjection H X).left.fiber (X.pointMap x)) : X.scheme :=
  productFirstFibreHomeomorph X X x
    (((fst X.toOver X.toOver).left.fiberHomeo (X.pointMap x)).symm
      (relationFibreLift H X x ((orbitRelationProjection H X).left.fiberHomeo (X.pointMap x) z)))

/-- The relation fibre map is the second coordinate of the relation inclusion. -/
theorem relationFibreMap_apply (x : X.points)
    (z : (orbitRelationProjection H X).left.fiber (X.pointMap x)) :
    relationFibreMap H X x z = (snd X.toOver X.toOver).left
      ((orbitRelationInclusion H X).left ((orbitRelationProjection H X).left.fiberι
        (X.pointMap x) z)) := by
  simp only [relationFibreMap, productFirstFibreHomeomorph_apply,
    Scheme.Hom.fiberι_fiberHomeo_symm, relationFibreLift, Scheme.Hom.fiberHomeo_apply]

/-- Every orbit relation fibre embeds as a closed subspace of the original variety. -/
theorem relationFibreMap_isClosedEmbedding (x : X.points) :
    IsClosedEmbedding (relationFibreMap H X x) :=
  (productFirstFibreHomeomorph X X x).isClosedEmbedding.comp
    (((fst X.toOver X.toOver).left.fiberHomeo (X.pointMap x)).symm.isClosedEmbedding.comp
      ((relationFibreLift_closed H X x).comp
        ((orbitRelationProjection H X).left.fiberHomeo (X.pointMap x)).isClosedEmbedding))

/-- The closed image of a relation fibre has the fibre's Krull dimension. -/
theorem relationFibreMap_dim (x : X.points) :
    topologicalKrullDim (Set.range (relationFibreMap H X x)) =
      topologicalKrullDim ((orbitRelationProjection H X).left.fiber (X.pointMap x)) := by
  let e := (relationFibreMap_isClosedEmbedding H X x).isEmbedding.toHomeomorph
  exact e.isHomeomorph.topologicalKrullDim_eq.symm

end

end GroupActions.Variety
