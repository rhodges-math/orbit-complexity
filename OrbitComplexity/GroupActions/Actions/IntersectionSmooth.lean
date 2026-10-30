import OrbitComplexity.GroupActions.Actions.Intersections
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Smooth covers of equivariant intersections

The equivariant intersection isomorphism identifies the product cover with a
pullback of the transverse action over the product of the two smooth sources.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
open CartesianMonoidalCategory MonoidalCategory
namespace GroupActions
noncomputable section
universe u

/-- A smooth transverse action gives a smooth group-product cover of the
equivariant pullback of two smooth sources. -/
theorem equivariantIntersection_smooth {S : Scheme.{u}} (B O F X Y : Over S)
    [GrpObj B] [GrpObj O] [ModObj B F] [ModObj O F] [ModObj B X] [ModObj O Y]
    (f : X ⟶ F) (g : Y ⟶ F) [IsModHom B f] [IsModHom O g]
    [Smooth X.hom] [Smooth Y.hom] [Smooth (transverseAction B O F).left] :
    Smooth (((B ⊗ O) ⊗ pullback f g).hom) := by
  let p := transverseAction B O F
  let k := f ⊗ₘ g
  have hp : IsPullback (pullback.fst p k).left (pullback.snd p k).left p.left k.left :=
    (IsPullback.of_hasPullback p k).map (Over.forget S)
  have : Smooth (pullback.snd p k).left :=
    MorphismProperty.of_isPullback hp inferInstance
  have : Smooth (X ⊗ Y).hom := by
    change Smooth (pullback.fst X.hom Y.hom ≫ X.hom)
    infer_instance
  have : Smooth (pullback p k).hom := by
    rw [← (pullback.snd p k).w]
    infer_instance
  let e := equivariantIntersectionIso B O F f g
  rw [← e.hom.w]
  infer_instance

end
end GroupActions
