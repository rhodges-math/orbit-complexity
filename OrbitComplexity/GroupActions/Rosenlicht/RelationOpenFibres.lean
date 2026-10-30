import OrbitComplexity.GroupActions.Rosenlicht.RelationVarieties
import OrbitComplexity.GroupActions.Varieties.GenericBaseFibres
import OrbitComplexity.GroupActions.Varieties.FiniteDimension

/-!
# Open parts of orbit relation fibres

Constructibility supplies an open part of the relation closure inside the
orbit relation. Over a nonempty open subset of the original variety, its fibres
have the same dimension as the fibres of the full relation closure.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- The orbit relation contains a nonempty open part of its reduced closure. -/
theorem exists_open_orbitRelation :
    ∃ U : (orbitRelationVariety H X).scheme.Opens,
      (U : Set (orbitRelationVariety H X).scheme).Nonempty ∧
        (U : Set (orbitRelationVariety H X).scheme) ⊆ Set.range (orbitRelationFactor H X).left := by
  have : IsIntegral (productVariety H X).scheme := product_integral H X
  obtain ⟨U, hU, hUne, hUr⟩ := exists_open_inter_range (orbitRelationFactor H X)
  rw [(orbitRelationFactor H X).left.denseRange.closure_range, Set.inter_univ] at hUne hUr
  exact ⟨⟨U, hU⟩, hUne, hUr⟩

/-- An open part contained in the relation has fibres of the full relation
closure's dimension over a nonempty open subset of the original variety. -/
theorem exists_open_relation_fibre_dims :
    ∃ U : (orbitRelationVariety H X).scheme.Opens,
      (U : Set (orbitRelationVariety H X).scheme).Nonempty ∧
      (U : Set (orbitRelationVariety H X).scheme) ⊆ Set.range (orbitRelationFactor H X).left ∧
      ∃ V : X.scheme.Opens, (V : Set X.scheme).Nonempty ∧ ∀ x ∈ V,
        (orbitRelationVariety H X).dim = X.dim +
          topologicalKrullDim ((orbitRelationProjection H X).left.fiber x) ∧
        topologicalKrullDim
          ((((orbitRelationVariety H X).openInclusion U) ≫
            orbitRelationProjection H X).left.fiber x) =
          topologicalKrullDim ((orbitRelationProjection H X).left.fiber x) := by
  obtain ⟨U, hU, hUr⟩ := exists_open_orbitRelation H X
  let R := orbitRelationVariety H X
  let O := R.openSubvariety U
  let g : O.toOver ⟶ X.toOver := R.openInclusion U ≫ orbitRelationProjection H X
  have : Nonempty (U : Scheme) := Set.nonempty_coe_sort.mpr hU
  have : IrreducibleSpace O.scheme := U.ι.isOpenEmbedding.irreducibleSpace
  have : IsDominant (R.openInclusion U).left :=
    Opens.isDominant_ι (U.isOpen.dense hU)
  have : IsDominant g.left := inferInstanceAs
    (IsDominant ((R.openInclusion U).left ≫ (orbitRelationProjection H X).left))
  obtain ⟨V₁, hV₁, hd₁⟩ := exists_open_dim_add R X (orbitRelationProjection H X)
  obtain ⟨V₂, hV₂, hd₂⟩ := exists_open_dim_add O X g
  refine ⟨U, hU, hUr, V₁ ⊓ V₂, ?_, ?_⟩
  · refine ⟨genericPoint X.scheme, ?_, ?_⟩
    · exact ((genericPoint_spec X.scheme).mem_open_set_iff V₁.isOpen).mpr
        (by simpa only [Set.univ_inter] using hV₁)
    · exact ((genericPoint_spec X.scheme).mem_open_set_iff V₂.isOpen).mpr
        (by simpa only [Set.univ_inter] using hV₂)
  · intro x hx
    refine ⟨hd₁ x hx.1, ?_⟩
    have hs := (hd₂ x hx.2).symm.trans ((R.openSubvariety_dim U hU).trans (hd₁ x hx.1))
    rw [← X.natDim_cast] at hs
    exact (ENat.WithBot.natCast_add_cancel).mp hs

end

end GroupActions.Variety
