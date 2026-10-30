import OrbitComplexity.FrobeniusSplitting.Normality.WeakNormal
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral closures of split rings

A finite normalization whose map on spectra is universally injective is trivial
when its base admits a Frobenius splitting. The splitting extends to the total
quotient ring, where the finite conductor argument applies.

## References

* Brion and Kumar, *Frobenius splitting methods in geometry and representation
  theory*, Proposition 1.2.5.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry

universe u

/-- A split ring with finite universally injective integral closure is integrally closed. -/
theorem isIntegrallyClosed_of_split {A : Type u} [CommRing A]
    {q : ℕ} [Fact q.Prime] [CharP A q] (splitting : RingSplitting A q)
    [Module.Finite A (integralClosure A (FractionRing A))]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom
      (algebraMap A (integralClosure A (FractionRing A)))))] : IsIntegrallyClosed A := by
  let K := FractionRing A
  let B := integralClosure A K
  let ambient := splitting.localize (S := K) (nonZeroDivisors A) (Fact.out : q.Prime).pos
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).2
    Subtype.val_injective
  have hsurj : Function.Surjective (algebraMap A B) :=
    surjective_of_finite_specMap splitting ambient
      (fun a ↦ splitting.localize_algebraMap (nonZeroDivisors A) (Fact.out : q.Prime).pos a)
  apply (isIntegrallyClosed_iff (K := K)).2
  intro x hx
  obtain ⟨a, ha⟩ := hsurj ⟨x, hx⟩
  exact ⟨a, congrArg Subtype.val ha⟩

end FrobeniusSplitting
