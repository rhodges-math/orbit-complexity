import OrbitComplexity.GroupActions.Actions.IdentityAction
import OrbitComplexity.GroupActions.Actions.ComponentIntersections
import OrbitComplexity.GroupActions.Actions.Stabilizers

/-! # Stabilizer dimension and the identity component

Translation by a stabilizer point preserves the stabilizer fibre. Its dimension is
therefore the dimension of its intersection with the identity component.

## Main results

* `GroupActions.identity_stabilizer_dim`: restriction to the identity component preserves
  stabilizer dimension.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]

attribute [local instance] identityComponentAction

private theorem stabilizer_translation (x : X.points) (h : H.points)
    (hh : (Variety.orbitMorphism H X x).left (H.pointMap h) = X.pointMap x) :
    (leftTranslation H h).hom.left ''
      ((Variety.orbitMorphism H X x).left ⁻¹' {X.pointMap x}) =
        (Variety.orbitMorphism H X x).left ⁻¹' {X.pointMap x} := by
  let f := Variety.orbitMorphism H X x
  let t := Variety.translateMorphism H X h
  have hfix : t.left (X.pointMap x) = X.pointMap x := by
    rw [← Variety.pointMap_mapPoints, Variety.mapPoints_translateMorphism]
    rw [← Variety.pointMap_mapPoints, Variety.mapPoints_orbitMorphism] at hh
    exact hh
  have hf (z : H.scheme) :
      f.left ((leftTranslation H h).hom.left z) = t.left (f.left z) := by
    have he := congrArg Over.Hom.left (orbitMorphism_translation H X x h)
    exact congrArg (fun g : H.scheme ⟶ X.scheme ↦ g z) he
  have hiff (z : H.scheme) :
      f.left ((leftTranslation H h).hom.left z) = X.pointMap x ↔
        f.left z = X.pointMap x := by
    rw [hf]
    constructor
    · intro he
      apply ((Over.forget _).mapIso (Variety.translationIso H X h)).hom.homeomorph.injective
      exact he.trans hfix.symm
    · intro he
      rw [he, hfix]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (hiff w).mpr hw
  · intro hz
    obtain ⟨w, rfl⟩ := (leftTranslation H h).hom.left.surjective z
    exact ⟨w, (hiff w).mp hz, rfl⟩

/-- Restricting to the identity component preserves stabilizer dimension. -/
theorem identity_stabilizer_dim (x : X.points) :
    (stabilizerVariety (identityComponent H) X x).dim =
      (stabilizerVariety H X x).dim := by
  let f := Variety.orbitMorphism H X x
  let S : Set H.scheme := f.left ⁻¹' {X.pointMap x}
  have hS : IsClosed S :=
    (X.pointsEquivClosedPoints x).property.preimage f.left.continuous
  have hd := closed_dim_eq_identity_inter H S hS (stabilizer_translation H X x)
  have hf : (Variety.orbitMorphism (identityComponent H) X x).left ⁻¹' {X.pointMap x} =
      (identityInclusion H).left ⁻¹' S := by
    rw [identity_orbitMorphism]
    rfl
  calc
    (stabilizerVariety (identityComponent H) X x).dim =
        topologicalKrullDim ((Variety.orbitMorphism (identityComponent H) X x).left ⁻¹'
          {X.pointMap x}) :=
      (stabilizerHomeomorph (identityComponent H) X x).isHomeomorph.topologicalKrullDim_eq
    _ = topologicalKrullDim ↥(S ∩ connectedComponent (H.pointMap 1)) := by
      rw [hf, (identityInclusion H).left.isEmbedding.topologicalKrullDim_preimage,
        identityInclusion_range]
    _ = topologicalKrullDim S := hd.symm
    _ = (stabilizerVariety H X x).dim :=
      (stabilizerHomeomorph H X x).isHomeomorph.topologicalKrullDim_eq.symm

end

end GroupActions
