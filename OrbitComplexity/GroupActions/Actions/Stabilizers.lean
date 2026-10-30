import OrbitComplexity.GroupActions.Actions.Orbits
import OrbitComplexity.GroupActions.Varieties.Subvarieties
import Mathlib.AlgebraicGeometry.Fiber

/-! # Stabilizers as varieties

The inverse image of a rational point under its orbit morphism is closed. Its reduced
induced variety has exactly the rational points of the stabilizer, and the same dimension
as the scheme-theoretic fibre of the orbit morphism.

## Main definitions

* `GroupActions.stabilizerVariety`: the reduced variety on the stabilizer fibre.
* `GroupActions.stabilizerInclusion`: its inclusion into the acting group.

## Main results

* `GroupActions.stabilizerPointsEquiv`: stabilizer-variety points identify with the stabilizer.
* `GroupActions.stabilizerVariety_dim`: reduction preserves the fibre dimension.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]

private def stabilizerClosed (x : X.points) : Closeds H.scheme :=
  ⟨(Variety.orbitMorphism H X x).left ⁻¹' {X.pointMap x},
    (X.pointsEquivClosedPoints x).property.preimage (Variety.orbitMorphism H X x).left.continuous⟩

/-- The reduced induced variety on the stabilizer fibre of an orbit morphism. -/
def stabilizerVariety (x : X.points) : Variety K := H.closedSubvariety (stabilizerClosed H X x)

/-- The inclusion of the stabilizer variety into the acting group. -/
def stabilizerInclusion (x : X.points) : (stabilizerVariety H X x).toOver ⟶ H.toOver :=
  H.closedInclusion (stabilizerClosed H X x)

/-- The inclusion of the stabilizer variety is a closed immersion. -/
instance stabilizerInclusion_isClosedImmersion (x : X.points) :
    IsClosedImmersion (stabilizerInclusion H X x).left :=
  inferInstanceAs (IsClosedImmersion (H.closedInclusion (stabilizerClosed H X x)).left)

/-- The image of the stabilizer inclusion is the fibre over the fixed rational point. -/
theorem stabilizerInclusion_range (x : X.points) :
    Set.range ((stabilizerInclusion H X x).left : (stabilizerVariety H X x).scheme → H.scheme) =
      (Variety.orbitMorphism H X x).left ⁻¹' {X.pointMap x} :=
  H.closedInclusion_range (stabilizerClosed H X x)

/-- The stabilizer variety has the topology induced on the set-theoretic fibre. -/
def stabilizerHomeomorph (x : X.points) : (stabilizerVariety H X x).scheme ≃ₜ
    (Variety.orbitMorphism H X x).left ⁻¹' {X.pointMap x} :=
  (stabilizerInclusion H X x).left.isEmbedding.toHomeomorph.trans
    (.setCongr (stabilizerInclusion_range H X x))

private theorem stabilizer_point_mem (x : X.points) (p : (stabilizerVariety H X x).points) :
    Variety.mapPoints (stabilizerInclusion H X x) p ∈ MulAction.stabilizer H.points x := by
  have hp : H.pointMap (Variety.mapPoints (stabilizerInclusion H X x) p) ∈
      (Variety.orbitMorphism H X x).left ⁻¹' {X.pointMap x} := by
    rw [← stabilizerInclusion_range H X x, Variety.pointMap_mapPoints]
    exact ⟨(stabilizerVariety H X x).pointMap p, rfl⟩
  apply MulAction.mem_stabilizer_iff.mpr
  apply X.pointMap_injective
  change (Variety.orbitMorphism H X x).left
    (H.pointMap (Variety.mapPoints (stabilizerInclusion H X x) p)) = X.pointMap x at hp
  rw [← Variety.pointMap_mapPoints, Variety.mapPoints_orbitMorphism] at hp
  exact hp

/-- Rational points of the stabilizer variety identify with the stabilizer subgroup. -/
def stabilizerPointsEquiv (x : X.points) :
    (stabilizerVariety H X x).points ≃ MulAction.stabilizer H.points x := by
  let F : (stabilizerVariety H X x).points → MulAction.stabilizer H.points x :=
    fun p ↦ ⟨Variety.mapPoints (stabilizerInclusion H X x) p, stabilizer_point_mem H X x p⟩
  apply Equiv.ofBijective F
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply (cancel_mono (stabilizerInclusion H X x).left).mp
    exact congrArg Subtype.val (congrArg Subtype.val hpq)
  · intro h
    have hmem : H.pointMap h.val ∈ Set.range ((stabilizerInclusion H X x).left :
        (stabilizerVariety H X x).scheme → H.scheme) := by
      rw [stabilizerInclusion_range]
      change (Variety.orbitMorphism H X x).left (H.pointMap h.val) = X.pointMap x
      rw [← Variety.pointMap_mapPoints, Variety.mapPoints_orbitMorphism]
      exact congrArg X.pointMap (MulAction.mem_stabilizer_iff.mp h.property)
    obtain ⟨p, hp⟩ := Variety.exists_mapPoints_eq (stabilizerInclusion H X x) h.val hmem
    exact ⟨p, Subtype.ext hp⟩

/-- The stabilizer variety is nonempty because the identity element fixes the point. -/
instance stabilizerVarietyNonempty (x : X.points) : Nonempty (stabilizerVariety H X x).scheme :=
  ⟨(stabilizerVariety H X x).pointMap ((stabilizerPointsEquiv H X x).symm 1)⟩

/-- The reduced stabilizer variety has the dimension of the scheme-theoretic fibre. -/
theorem stabilizerVariety_dim (x : X.points) : (stabilizerVariety H X x).dim =
    topologicalKrullDim ((Variety.orbitMorphism H X x).left.fiber (X.pointMap x)) := by
  let e := (Variety.orbitMorphism H X x).left.fiberHomeo (X.pointMap x)
  have hf := e.isHomeomorph.topologicalKrullDim_eq
  exact (stabilizerHomeomorph H X x).isHomeomorph.topologicalKrullDim_eq.trans hf.symm

end

end GroupActions
