import TauCeti.RingTheory.IntegralClosure.MvPolynomial
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.NoetherNormalization

/-!
# Finite normalization of affine coordinate rings

Noether normalization makes a finite-type domain finite over an injected polynomial
ring. Its fraction field is a finite extension of the polynomial fraction field.
Finiteness of polynomial normalization then descends through the integral tower.
-/

namespace FrobeniusSplitting

/-- The normalization of a finite type domain over a field is finite. -/
theorem finite_normalization {k R : Type*} [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] :
    Module.Finite R (integralClosure R (FractionRing R)) := by
  obtain ⟨n, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg k R
  let P := MvPolynomial (Fin n) k
  let K := FractionRing P
  let L := FractionRing R
  let C := integralClosure R L
  let : Algebra P R := g.toRingHom.toAlgebra
  have : FaithfulSMul P R := (faithfulSMul_iff_algebraMap_injective P R).mpr hg
  have : Module.Finite P R := hfinite
  let : Algebra K L := FractionRing.liftAlgebra P L
  have : IsScalarTower P K L := FractionRing.isScalarTower_liftAlgebra P L
  have : FiniteDimensional K L := Module.Finite.of_isLocalization P R (nonZeroDivisors P)
  have : IsIntegralClosure C P L := TauCeti.IsIntegralClosure.tower_bot (A := R)
  have : Module.Finite P C := TauCeti.IsIntegralClosure.finite_mvPolynomial k K L C
  exact Module.Finite.of_restrictScalars_finite P R C

end FrobeniusSplitting
