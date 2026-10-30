import OrbitComplexity.GroupActions.Actions.Components
import OrbitComplexity.GroupActions.Varieties.ClosedPoints

/-! # Dimensions of group components

Translation by a rational point takes the identity component to its component. Each
component contains a rational point, so all components have the ambient group dimension.

## Main results

* `GroupActions.identityComponent_dim`: the identity component has the group dimension.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H : Variety K) [GrpObj H.toOver]

omit [IsAlgClosed K] in
private theorem translation_unit (h : H.points) :
    (leftTranslation H h).hom.left (H.pointMap 1) = H.pointMap h := by
  rw [← Variety.pointMap_mapPoints, leftTranslation_points, mul_one]

omit [IsAlgClosed K] in
/-- Left translation takes the identity component to the translator's component. -/
theorem translation_component (h : H.points) :
    (leftTranslation H h).hom.left '' connectedComponent (H.pointMap 1) =
      connectedComponent (H.pointMap h) := by
  let e := ((Over.forget _).mapIso (leftTranslation H h)).hom.homeomorph
  have he := e.image_connectedComponentIn (x := H.pointMap 1) (Set.mem_univ _)
  simp only [connectedComponentIn_univ, Set.image_univ, e.surjective.range_eq] at he
  change (leftTranslation H h).hom.left '' connectedComponent (H.pointMap 1) =
    connectedComponent ((leftTranslation H h).hom.left (H.pointMap 1)) at he
  rw [translation_unit] at he
  exact he

omit [IsAlgClosed K] in
private theorem component_point_dim (h : H.points) :
    (groupComponent H (H.pointMap h)).dim = (identityComponent H).dim := by
  let e := ((Over.forget _).mapIso (leftTranslation H h)).hom.homeomorph
  let q := (e.image (connectedComponent (H.pointMap 1))).trans
    (Homeomorph.setCongr (translation_component H h))
  exact q.isHomeomorph.topologicalKrullDim_eq.symm

omit [GrpObj H.toOver] in
/-- Every connected component contains the image of a rational point. -/
theorem exists_point_component (x : H.scheme) :
    ∃ h : H.points, connectedComponent (H.pointMap h) = connectedComponent x := by
  have : JacobsonSpace H.scheme := LocallyOfFiniteType.jacobsonSpace H.toSpec
  obtain ⟨p, hp, hpc⟩ := nonempty_inter_closedPoints
    (show (connectedComponent x).Nonempty from ⟨x, mem_connectedComponent⟩)
    isClosed_connectedComponent.isLocallyClosed
  obtain ⟨h, hh⟩ := H.pointsEquivClosedPoints.surjective ⟨p, hpc⟩
  have he : H.pointMap h = p := congrArg Subtype.val hh
  refine ⟨h, ?_⟩
  have hc : connectedComponent (H.pointMap h) = connectedComponent x := by
    rw [he]
    exact (connectedComponent_eq hp).symm
  exact hc

private theorem component_dim_eq (x : H.scheme) :
    (groupComponent H x).dim = (identityComponent H).dim := by
  obtain ⟨h, hc⟩ := exists_point_component H x
  have hd := component_point_dim H h
  change topologicalKrullDim (connectedComponent (H.pointMap h)) = _ at hd
  rw [hc] at hd
  exact hd

/-- The identity component has the same dimension as the whole group variety. -/
theorem identityComponent_dim : (identityComponent H).dim = H.dim := by
  have : Nonempty H.scheme := ⟨H.pointMap 1⟩
  change _ = topologicalKrullDim H.scheme
  rw [TauCeti.topologicalKrullDim_eq_iSup_of_isOpenEmbedding
    (Y := fun x : H.scheme ↦ connectedComponent x) (fun _ ↦ Subtype.val)
    (fun _ ↦ isOpen_connectedComponent.isOpenEmbedding_subtypeVal)
    (fun x ↦ ⟨x, ⟨x, mem_connectedComponent⟩, rfl⟩)]
  have hd (x : H.scheme) : topologicalKrullDim (connectedComponent x) =
      (identityComponent H).dim := component_dim_eq H x
  simp only [hd, iSup_const]

omit [GrpObj H.toOver] in
/-- Finitely many rational-point components cover the group variety. -/
theorem exists_finite_components :
    ∃ s : Finset H.points, ∀ x : H.scheme,
      ∃ h ∈ s, x ∈ connectedComponent (H.pointMap h) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun h : H.points ↦ connectedComponent (H.pointMap h))
    (fun _ ↦ isOpen_connectedComponent) (by
      intro x _
      obtain ⟨h, hh⟩ := exists_point_component H x
      exact Set.mem_iUnion.mpr ⟨h, hh.symm ▸ mem_connectedComponent⟩)
  refine ⟨s, fun x ↦ ?_⟩
  simpa only [Set.mem_iUnion, exists_prop] using hs (Set.mem_univ x)

omit [IsAlgClosed K] in
/-- Translating the identity-component inclusion gives the component of the translator. -/
theorem translated_identity_range (h : H.points) :
    Set.range ((identityInclusion H ≫ (leftTranslation H h).hom).left :
      (identityComponent H).scheme → H.scheme) = connectedComponent (H.pointMap h) := by
  change Set.range ((leftTranslation H h).hom.left ∘ (identityInclusion H).left) = _
  rw [Set.range_comp, identityInclusion_range, translation_component]

/-- A rational point of a component is a translate of an identity-component point. -/
theorem exists_identity_translate (h p : H.points)
    (hp : H.pointMap p ∈ connectedComponent (H.pointMap h)) :
    ∃ q : (identityComponent H).points, h * Variety.mapPoints (identityInclusion H) q = p := by
  obtain ⟨q, hq⟩ := Variety.exists_mapPoints_eq
    (identityInclusion H ≫ (leftTranslation H h).hom) p
    (by rw [translated_identity_range]; exact hp)
  rw [Variety.mapPoints_comp, leftTranslation_points] at hq
  exact ⟨q, hq⟩

end

end GroupActions
