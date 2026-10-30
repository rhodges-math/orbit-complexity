import OrbitComplexity.GroupActions.Actions.ComponentDimensions

/-! # Dimensions of translation-invariant closed sets

A closed set preserved by translation by each of its rational points has the dimension of
its intersection with the identity component. The component intersections form an open
cover, and each nonempty intersection is a translate of the identity-component intersection.

## Main results

* `GroupActions.closed_dim_eq_identity_inter`: reduction to the identity component for
  translation-invariant closed sets.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H : Variety K) [GrpObj H.toOver]

/-- A translation-invariant closed set has the dimension of its identity-component part. -/
theorem closed_dim_eq_identity_inter (S : Set H.scheme) (hS : IsClosed S)
    (htrans : ∀ h : H.points, H.pointMap h ∈ S →
      (leftTranslation H h).hom.left '' S = S) :
    topologicalKrullDim S =
      topologicalKrullDim ↥(S ∩ connectedComponent (H.pointMap 1)) := by
  refine le_antisymm ?_
    (IsEmbedding.inclusion Set.inter_subset_left).isInducing.topologicalKrullDim_le
  rw [TauCeti.topologicalKrullDim_eq_iSup_of_isOpenEmbedding
    (Y := fun x : H.scheme ↦ (Subtype.val : S → H.scheme) ⁻¹' connectedComponent x)
    (fun _ ↦ Subtype.val)
    (fun _ ↦ (isOpen_connectedComponent.preimage
      continuous_subtype_val).isOpenEmbedding_subtypeVal)
    (fun z ↦ ⟨z.val, ⟨z, mem_connectedComponent⟩, rfl⟩)]
  refine iSup_le fun x ↦ ?_
  by_cases hne : (S ∩ connectedComponent x).Nonempty
  · have : JacobsonSpace H.scheme := LocallyOfFiniteType.jacobsonSpace H.toSpec
    obtain ⟨p, hp, hpc⟩ := nonempty_inter_closedPoints hne
      (hS.isLocallyClosed.inter isOpen_connectedComponent.isLocallyClosed)
    obtain ⟨h, hh⟩ := H.pointsEquivClosedPoints.surjective ⟨p, hpc⟩
    have he : H.pointMap h = p := congrArg Subtype.val hh
    have hc : connectedComponent (H.pointMap h) = connectedComponent x := by
      rw [he]
      exact (connectedComponent_eq hp.2).symm
    let e := ((Over.forget _).mapIso (leftTranslation H h)).hom.homeomorph
    have hi : e '' (S ∩ connectedComponent (H.pointMap 1)) = S ∩ connectedComponent x := by
      rw [Set.image_inter e.injective]
      change (leftTranslation H h).hom.left '' S ∩
        (leftTranslation H h).hom.left '' connectedComponent (H.pointMap 1) = _
      rw [htrans h (he ▸ hp.1), translation_component, hc]
    have hd := ((e.image (S ∩ connectedComponent (H.pointMap 1))).trans
      (Homeomorph.setCongr hi)).isHomeomorph.topologicalKrullDim_eq
    rw [(IsEmbedding.subtypeVal (p := (· ∈ S))).topologicalKrullDim_preimage,
      Subtype.range_coe_subtype]
    have hcomm := (Homeomorph.setCongr
      (Set.inter_comm (connectedComponent x) S)).isHomeomorph.topologicalKrullDim_eq
    exact (hcomm.trans hd.symm).le
  · have : IsEmpty ((Subtype.val : S → H.scheme) ⁻¹' connectedComponent x) := by
      refine ⟨fun z ↦ hne ⟨z.val.val, z.val.property, z.property⟩⟩
    have : IsEmpty (IrreducibleCloseds
        ((Subtype.val : S → H.scheme) ⁻¹' connectedComponent x)) := by
      refine ⟨fun Z ↦ ?_⟩
      obtain ⟨z, -⟩ := Z.isIrreducible.nonempty
      exact isEmptyElim z
    rw [topologicalKrullDim, Order.krullDim_eq_bot]
    exact bot_le

end

end GroupActions
