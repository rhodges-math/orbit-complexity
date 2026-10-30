import OrbitComplexity.FrobeniusSplitting.Normality.ConnectedFibers
import OrbitComplexity.FrobeniusSplitting.Normality.IntegralClosure
import OrbitComplexity.FrobeniusSplitting.Normality.Normalization

/-!
# Normality of split affine domains

Finite normalization and the conductor argument reduce normality of a split
finite-type domain to universal injectivity of its normalization. Connected fibers
of a morphism covering the normalization provide that universal injectivity.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory
universe u

/-- A finite-type split domain is normal when its normalization is universally injective. -/
theorem isIntegrallyClosed_of_split_ft {k : Type*} [Field k]
    {R : Type u} [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    {q : ℕ} [Fact q.Prime] [CharP R q] (splitting : RingSplitting R q)
    [UniversallyInjective (Spec.map (CommRingCat.ofHom
      (algebraMap R (integralClosure R (FractionRing R)))))] : IsIntegrallyClosed R := by
  have := finite_normalization (k := k) (R := R)
  exact isIntegrallyClosed_of_split splitting

/-- A split finite-type domain is normal if its normalization is covered by a
morphism whose composite to the original spectrum has geometrically connected fibers. -/
theorem isIntegrallyClosed_of_connected {k : Type u} [Field k]
    {R : Type u} [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    {q : ℕ} [Fact q.Prime] [CharP R q] (splitting : RingSplitting R q)
    {X : Scheme.{u}}
    (h : X ⟶ Spec (.of (integralClosure R (FractionRing R)))) [Surjective h]
    [GeometricallyConnected (h ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (integralClosure R (FractionRing R)))))] : IsIntegrallyClosed R := by
  let C := integralClosure R (FractionRing R)
  let g := Spec.map (CommRingCat.ofHom (algebraMap R C))
  have := finite_normalization (k := k) (R := R)
  have : IsFinite g := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R C)))
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : UniversallyInjective g := universallyInjective_of_connectedFibers h g
  exact isIntegrallyClosed_of_split_ft (k := k) splitting

end FrobeniusSplitting
