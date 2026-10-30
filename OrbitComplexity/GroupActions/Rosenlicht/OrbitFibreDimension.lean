import OrbitComplexity.GroupActions.Rosenlicht.OrbitFibreImages
import OrbitComplexity.GroupActions.Rosenlicht.OpenFibreMaps
import OrbitComplexity.GroupActions.Rosenlicht.RelationOpenFibres

/-!
# General fibres of the orbit relation

An open part of the relation maps fibrewise into an orbit. Its fibre dimension
agrees with that of the relation closure over a nonempty open subset. Together
with the closed embedding of a full relation fibre, this gives the general
orbit dimension from the relation projection.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- A fibre of an open part contained in the relation has at most the orbit dimension. -/
theorem openRelationFibre_dim_le
    (U : (orbitRelationVariety H X).scheme.Opens)
    (hUr : (U : Set (orbitRelationVariety H X).scheme) ⊆
      Set.range (orbitRelationFactor H X).left) (x : X.points) :
    topologicalKrullDim
      ((((orbitRelationVariety H X).openInclusion U) ≫
        orbitRelationProjection H X).left.fiber (X.pointMap x)) ≤ orbitDim H X x := by
  let f := (orbitRelationProjection H X).left
  let g := U.ι ≫ f
  let e : g.fiber (X.pointMap x) → X.scheme :=
    relationFibreMap H X x ∘ openFibreMap f U (X.pointMap x)
  have he : IsEmbedding e := (relationFibreMap_isClosedEmbedding H X x).isEmbedding.comp
    (openFibreMap_isEmbedding f U (X.pointMap x))
  have hm : ∀ z, e z ∈ orbitClosure H X x := by
    intro z
    have hz : f.fiberι (X.pointMap x) (openFibreMap f U (X.pointMap x) z) ∈
        Set.range (orbitRelationFactor H X).left := by
      rw [openFibreMap_apply]
      exact hUr (g.fiberι (X.pointMap x) z).property
    have hi := relationFibre_image_of_range H X x (openFibreMap f U (X.pointMap x) z) hz
    rw [orbitClosure_eq]
    exact subset_closure hi
  have hc : IsEmbedding ((orbitClosure H X x).codRestrict e hm) :=
    he.codRestrict (orbitClosure H X x) hm
  change topologicalKrullDim (g.fiber (X.pointMap x)) ≤
    topologicalKrullDim (orbitClosure H X x)
  exact hc.isInducing.topologicalKrullDim_le

/-- Over a nonempty open subset, relation fibres and rational-point orbits
have equal dimension, and the relation projection satisfies the dimension formula. -/
theorem exists_open_orbit_fibre_dim :
    ∃ V : X.scheme.Opens, (V : Set X.scheme).Nonempty ∧
      ∀ x : X.points, X.pointMap x ∈ V →
        orbitDim H X x =
          topologicalKrullDim ((orbitRelationProjection H X).left.fiber (X.pointMap x)) ∧
        (orbitRelationVariety H X).dim = X.dim + orbitDim H X x := by
  obtain ⟨U, _, hUr, V, hV, hd⟩ := exists_open_relation_fibre_dims H X
  refine ⟨V, hV, ?_⟩
  intro x hx
  obtain ⟨hd, he⟩ := hd (X.pointMap x) hx
  have hl := openRelationFibre_dim_le H X U hUr x
  rw [he] at hl
  have hdim := le_antisymm (orbitDim_le_relationFibre H X x) hl
  exact ⟨hdim, by simpa only [hdim] using hd⟩

end

end GroupActions.Variety
