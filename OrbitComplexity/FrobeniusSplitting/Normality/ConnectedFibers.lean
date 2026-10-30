import OrbitComplexity.FrobeniusSplitting.Normality.Scheme
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Connected fibers and finite factors

The image of a connected fiber in a discrete quasi-finite fiber is a single point.
A surjective map to the factor therefore forces injectivity. Applying the argument after
base change gives universal injectivity. A finite generically invertible factor onto a split
scheme is therefore an isomorphism.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

/-- A quasi-finite factor of a morphism with connected fibers is injective when the
map to the factor is surjective. -/
theorem injective_of_connectedFibers {X Z Y : Scheme} (h : X ⟶ Z) (g : Z ⟶ Y)
    [Surjective h] [LocallyQuasiFinite g] [GeometricallyConnected (h ≫ g)] :
    Function.Injective g := by
  intro z₁ z₂ hz
  have heq : h '' ((h ≫ g) ⁻¹' {g z₁}) = g ⁻¹' {g z₁} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hx
      obtain ⟨x, rfl⟩ := h.surjective z
      exact ⟨x, hx, rfl⟩
  have hconn := ((h ≫ g).isConnected_preimage_singleton (g z₁)).image
    h h.continuous.continuousOn
  rw [heq] at hconn
  exact (hconn.2.isDiscrete_iff_subsingleton.mp (g.isDiscrete_preimage_singleton _))
    (by simp) (by simpa using hz.symm)

universe u

/-- A quasi-finite factor of a geometrically connected morphism is universally injective
when its source is covered by a surjective morphism. -/
theorem universallyInjective_of_connectedFibers {X Z Y : Scheme} (h : X ⟶ Z) (g : Z ⟶ Y)
    [Surjective h] [LocallyQuasiFinite g] [GeometricallyConnected (h ≫ g)] :
    UniversallyInjective g := by
  constructor
  apply MorphismProperty.universally_mk'
  intro T f _
  let g' := pullback.fst f g
  let h' := pullback.fst (pullback.snd f g) h
  have hp : IsPullback (h' ≫ g') (pullback.snd (pullback.snd f g) h) f (h ≫ g) :=
    (IsPullback.of_hasPullback (pullback.snd f g) h).paste_horiz
      (IsPullback.of_hasPullback f g)
  have : Surjective h' := inferInstance
  have : LocallyQuasiFinite g' := inferInstance
  have : GeometricallyConnected (h' ≫ g') :=
    MorphismProperty.of_isPullback hp.flip inferInstance
  exact injective_of_connectedFibers h' g'


end FrobeniusSplitting
