import OrbitComplexity.GroupActions.Actions.OrbitVariety
import OrbitComplexity.GroupActions.Actions.Stabilizers
import OrbitComplexity.GroupActions.Actions.Translations
import OrbitComplexity.GroupActions.Varieties.FibreIsomorphisms

/-! # Dimensions of the rational fibres of an orbit projection

Left translation identifies the fibres of an orbit morphism over rational points in its
orbit. Restricting its codomain to the orbit variety preserves those fibres. Each such
fibre therefore has the dimension of the stabilizer variety.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]

private theorem projection_preimage (x : X.points) (y : (orbitVariety H X x).scheme) :
    (orbitProjection H X x).left ⁻¹' {y} = (Variety.orbitMorphism H X x).left ⁻¹'
      {(orbitInclusion H X x).left y} := by
  ext h
  change (orbitProjection H X x).left h = y ↔
    (Variety.orbitMorphism H X x).left h = (orbitInclusion H X x).left y
  have he : (orbitInclusion H X x).left ((orbitProjection H X x).left h) =
      (Variety.orbitMorphism H X x).left h :=
    congrArg (fun m : H.scheme ⟶ X.scheme ↦ m h)
      (congrArg Over.Hom.left (orbitProjection_fac H X x))
  rw [← he]
  exact (orbitInclusion H X x).left.isEmbedding.injective.eq_iff.symm

/-- The orbit projection and the original orbit morphism have homeomorphic corresponding fibres. -/
def orbitProjectionFiberHomeomorph (x : X.points) (y : (orbitVariety H X x).scheme) :
    (orbitProjection H X x).left.fiber y ≃ₜ
      (Variety.orbitMorphism H X x).left.fiber ((orbitInclusion H X x).left y) :=
  ((orbitProjection H X x).left.fiberHomeo y).trans
    ((Homeomorph.setCongr (projection_preimage H X x y)).trans
      ((Variety.orbitMorphism H X x).left.fiberHomeo _).symm)

/-- Every rational fibre of the orbit projection has stabilizer dimension. -/
theorem orbitProjection_fibre_dim (x : X.points) (y : (orbitVariety H X x).points) :
    (stabilizerVariety H X x).dim = topologicalKrullDim
      ((orbitProjection H X x).left.fiber ((orbitVariety H X x).pointMap y)) := by
  obtain ⟨h, hh⟩ := orbitProjection_points_surjective H X x y
  have hp := congrArg (Variety.mapPoints (orbitInclusion H X x)) hh
  rw [← Variety.mapPoints_comp, orbitProjection_fac, Variety.mapPoints_orbitMorphism] at hp
  have hy := congrArg X.pointMap hp
  rw [Variety.pointMap_mapPoints] at hy
  let e := (Over.forget _).mapIso (leftTranslation H h)
  let e' := (Over.forget _).mapIso (Variety.translationIso H X h)
  have hs : e.hom ≫ (Variety.orbitMorphism H X x).left =
      (Variety.orbitMorphism H X x).left ≫ e'.hom :=
    congrArg Over.Hom.left (orbitMorphism_translation H X x h)
  have hd := fibre_dim_of_iso (Variety.orbitMorphism H X x).left
    (Variety.orbitMorphism H X x).left e e' hs (X.pointMap x)
  have he : e'.hom (X.pointMap x) = X.pointMap (h • x) := by
    change (Variety.translateMorphism H X h).left (X.pointMap x) = X.pointMap (h • x)
    rw [← Variety.pointMap_mapPoints, Variety.mapPoints_translateMorphism]
  rw [he, hy] at hd
  exact (stabilizerVariety_dim H X x).trans (hd.trans
    (orbitProjectionFiberHomeomorph H X x _).isHomeomorph.topologicalKrullDim_eq.symm)

end

end GroupActions
