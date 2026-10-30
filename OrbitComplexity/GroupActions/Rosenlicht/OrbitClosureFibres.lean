import OrbitComplexity.GroupActions.Rosenlicht.OrbitFibreImages
import OrbitComplexity.GroupActions.Rosenlicht.RelationOpenFibres
import OrbitComplexity.GroupActions.Rosenlicht.DenseFibres

/-!
# Orbit closures as fibres of the orbit relation
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions.Variety

noncomputable section

universe u

/-- On a nonempty open part of an irreducible variety, the fibre of the orbit
relation closure is the closure of the corresponding orbit. -/
theorem exists_open_orbitClosure_fibres {K : Type u} [Field K] [IsAlgClosed K]
    (H X : GroupActions.Variety K) [GrpObj H.toOver] [ModObj H.toOver X.toOver]
    [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme] :
    ∃ V : X.scheme.Opens, (V : Set X.scheme).Nonempty ∧ ∀ x : X.points,
      X.pointMap x ∈ V → orbitClosure H X x = Set.range (relationFibreMap H X x) := by
  obtain ⟨U, hU, hUr⟩ := exists_open_orbitRelation H X
  obtain ⟨V, hV, hD⟩ := exists_open_dense_fibres (orbitRelationVariety H X) X
    (orbitRelationProjection H X) U hU
  refine ⟨V, hV, ?_⟩
  intro x hx
  apply Set.Subset.antisymm
  · rw [orbitClosure_eq]
    exact closure_minimal (orbitImage_subset_relationFibre H X x)
      (relationFibreMap_isClosedEmbedding H X x).isClosed_range
  · rintro y ⟨z, rfl⟩
    let h := (orbitRelationProjection H X).left.fiberHomeo (X.pointMap x)
    let S := h.symm '' {r : (orbitRelationProjection H X).left ⁻¹' {X.pointMap x} |
      r.val ∈ U}
    have hS : Dense S :=
      h.symm.surjective.denseRange.dense_image h.symm.continuous (hD (X.pointMap x) hx)
    have hsub : relationFibreMap H X x '' S ⊆ Set.range (orbitMorphism H X x).left := by
      rintro y ⟨r, ⟨q, hq, rfl⟩, rfl⟩
      apply relationFibre_image_of_range H X x
      rw [show (orbitRelationProjection H X).left.fiberι (X.pointMap x) (h.symm q) =
        q.val from (orbitRelationProjection H X).left.fiberι_fiberHomeo_symm _ _]
      exact hUr hq
    rw [orbitClosure_eq]
    apply closure_mono hsub
    exact mem_closure_image
      (relationFibreMap_isClosedEmbedding H X x).continuous.continuousAt (hS z)

end

end GroupActions.Variety
