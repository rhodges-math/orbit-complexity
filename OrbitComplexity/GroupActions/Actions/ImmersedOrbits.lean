import OrbitComplexity.GroupActions.Varieties.ImmersionDimension
import OrbitComplexity.GroupActions.Actions.LocallyClosed

/-! # Orbit dimensions in immersed varieties

An immersion preserves the dimension of the closure of an orbit of an irreducible group.
The target variety need not carry a group action.

## Main results

* `GroupActions.orbit_image_dim`: orbit image dimension is unchanged by an immersion.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

/-- Immersing a variety preserves the dimension of each orbit of an irreducible group. -/
theorem orbit_image_dim {K : Type u} [Field K] [IsAlgClosed K] (H X Y : Variety K)
    [GrpObj H.toOver] [ModObj H.toOver X.toOver] [IrreducibleSpace H.scheme]
    (f : X.toOver ⟶ Y.toOver) [IsImmersion f.left] (x : X.points) :
    Y.subsetDim (Variety.mapPoints f '' MulAction.orbit H.points x) = orbitDim H X x := by
  have hI : IsIrreducible (Set.range
      ((Variety.orbitMorphism H X x).left : H.scheme → X.scheme)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ H.scheme).image
        (Variety.orbitMorphism H X x).left
        (Variety.orbitMorphism H X x).left.continuous.continuousOn
  have heq : Set.range (Variety.mapPoints (Variety.orbitMorphism H X x ≫ f)) =
      Variety.mapPoints f '' MulAction.orbit H.points x := by
    rw [show Variety.mapPoints (Variety.orbitMorphism H X x ≫ f) =
      Variety.mapPoints f ∘ Variety.mapPoints (Variety.orbitMorphism H X x) from
        funext (Variety.mapPoints_comp _ _), Set.range_comp, Variety.range_orbitMorphism]
  calc
    _ = Y.subsetDim (Set.range
        (Variety.mapPoints (Variety.orbitMorphism H X x ≫ f))) := congrArg Y.subsetDim heq.symm
    _ = X.subsetDim (Set.range (Variety.mapPoints (Variety.orbitMorphism H X x))) :=
      Variety.subsetDim_range_immersion _ f (orbitImage_locallyClosed H X x) hI
    _ = _ := congrArg X.subsetDim (Variety.range_orbitMorphism H X x)

end

end GroupActions
