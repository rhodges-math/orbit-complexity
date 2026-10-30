import OrbitComplexity.GroupActions.Actions.IdentityAction
import OrbitComplexity.GroupActions.Varieties.ClosedCoverDimension

/-! # Orbit dimension and the identity component

An orbit of the whole group is a finite union of translates of an identity-component
orbit. Their closures have equal dimension, and a finite closed cover preserves that bound.

## Main results

* `GroupActions.identity_orbitDim`: restriction to the identity component preserves orbit
  dimension.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]

attribute [local instance] identityComponentAction

omit [IsAlgClosed K] in
private theorem pointClosure_union {ι : Type*} (s : Finset ι) (T : ι → Set X.points) :
    X.pointClosure (⋃ i ∈ s, T i) = ⋃ i ∈ s, X.pointClosure (T i) := by
  simp only [Variety.pointClosure, Set.image_iUnion, Finset.closure_biUnion]

private theorem identity_orbit_subset (x : X.points) :
    MulAction.orbit (identityComponent H).points x ⊆ MulAction.orbit H.points x := by
  intro y hy
  obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.mp hy
  rw [identity_smul]
  exact MulAction.mem_orbit x _

private theorem exists_orbitClosure_union (x : X.points) :
    ∃ s : Finset H.points, orbitClosure H X x =
      ⋃ h ∈ s, (Variety.translateMorphism H X h).left ''
        orbitClosure (identityComponent H) X x := by
  obtain ⟨s, hs⟩ := exists_finite_orbit_union H X x
  refine ⟨s, ?_⟩
  rw [orbitClosure, hs, pointClosure_union]
  apply Set.iUnion_congr fun h ↦ Set.iUnion_congr fun _ ↦ ?_
  exact X.pointClosure_image (Variety.translationIso H X h) _

/-- Restricting an algebraic action to the identity component preserves orbit dimension. -/
theorem identity_orbitDim (x : X.points) :
    orbitDim (identityComponent H) X x = orbitDim H X x := by
  classical
  refine le_antisymm (X.subsetDim_mono (identity_orbit_subset H X x)) ?_
  obtain ⟨s, hs⟩ := exists_orbitClosure_union H X x
  let C := orbitClosure H X x
  let D := orbitClosure (identityComponent H) X x
  let S (h : s) : Set C := (Subtype.val : C → X.scheme) ⁻¹'
    ((Variety.translateMorphism H X h).left '' D)
  change topologicalKrullDim C ≤ topologicalKrullDim D
  apply topologicalKrullDim_le_closed_cover S
  · intro h
    let e := ((Over.forget _).mapIso (Variety.translationIso H X h)).hom.homeomorph
    exact (e.isClosedMap D isClosed_closure).preimage continuous_subtype_val
  · intro c
    have hc := (Set.ext_iff.mp hs c.val).mp c.property
    obtain ⟨h, hc⟩ := Set.mem_iUnion.mp hc
    obtain ⟨hh, hc⟩ := Set.mem_iUnion.mp hc
    exact ⟨⟨h, hh⟩, hc⟩
  · intro h
    let e := ((Over.forget _).mapIso (Variety.translationIso H X h)).hom.homeomorph
    calc
      topologicalKrullDim (S h) ≤ topologicalKrullDim (e '' D) :=
        ((IsEmbedding.subtypeVal (p := (· ∈ C))).restrictPreimage
          (e '' D)).isInducing.topologicalKrullDim_le
      _ = topologicalKrullDim D := (e.image D).isHomeomorph.topologicalKrullDim_eq.symm

end

end GroupActions
