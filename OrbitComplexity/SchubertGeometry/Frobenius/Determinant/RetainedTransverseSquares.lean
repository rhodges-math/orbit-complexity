import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.RootSquareSplitting
import OrbitComplexity.FrobeniusSplitting.Normality.ModelFlat
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Unit squares over a retained transverse coefficient algebra

A flat coefficient model embeds in its scalar extension. A polynomial whose
full scalar comparison is a unit times the square of its parameter therefore
has the same factorization before and after specialization. In odd
characteristic its normalized weighted splitting preserves the parameter ideal.
-/

set_option autoImplicit false
noncomputable section
universe u

open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry.DeterminantSection

open private polynomial_eq_square from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.RetainedRootSquares
open private weightedSpan squareWeight from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.RootSquareSplitting

variable {S K B A : Type u} [CommRing S] [CommRing K] [CommRing B] [CommRing A]
    [Algebra S K] [Algebra S B] [Algebra K A] [Algebra S A]
    [IsScalarTower S K A] [Module.Flat S B]

/-- A full unit-square comparison over an arbitrary coefficient algebra
retains its unit-square factorization on every specialization of the same
flat coefficient model. -/
theorem retainedPolynomial_square (e : K ⊗[S] B ≃ₐ[K] A)
    (hi : Function.Injective (algebraMap S K)) (P : Polynomial B) (w : Bˣ)
    (hP : Polynomial.map (tensorImageHom e).toRingHom P =
      Polynomial.C (tensorImageHom e (w : B)) * Polynomial.X ^ 2)
    {T : Type u} [CommRing T] (f : B →+* T) :
    ∃ v : Tˣ, Polynomial.map f P = Polynomial.C (v : T) * Polynomial.X ^ 2 := by
  have hf : Function.Injective (tensorImageHom e).toRingHom :=
    tensorImageHom_injective e hi
  have heq : P = Polynomial.C (w : B) * Polynomial.X ^ 2 :=
    polynomial_eq_square (tensorImageHom e).toRingHom hf P w hP
  refine ⟨Units.map f.toMonoidHom w, ?_⟩
  rw [heq, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  rfl

/-- The normalized weighted splitting associated to a retained transverse
unit-square polynomial preserves its parameter ideal over every odd
characteristic specialization, for an arbitrary original coefficient algebra. -/
theorem retainedPolynomial_compatible (e : K ⊗[S] B ≃ₐ[K] A)
    (hi : Function.Injective (algebraMap S K)) (P : Polynomial B) (w : Bˣ)
    (hP : Polynomial.map (tensorImageHom e).toRingHom P =
      Polynomial.C (tensorImageHom e (w : B)) * Polynomial.X ^ 2)
    {T : Type u} [CommRing T] (f : B →+* T) {p : ℕ} (hp : Odd p)
    (φ : FrobeniusLinearMap (Polynomial T) p)
    (hn : φ ((Polynomial.map f P) ^ ((p - 1) / 2)) = 1) :
    (φ.toSplitting ((Polynomial.map f P) ^ ((p - 1) / 2)) hn).IsCompatible
      (Ideal.span {Polynomial.X}) := by
  obtain ⟨v, hv⟩ := retainedPolynomial_square e hi P w hP f
  have hp0 : 0 < p := by
    obtain ⟨k, hk⟩ := hp
    omega
  have hweight : (Polynomial.map f P) ^ ((p - 1) / 2) =
      (Polynomial.C (v : T)) ^ ((p - 1) / 2) * Polynomial.X ^ (p - 1) := by
    rw [hv]
    exact squareWeight hp Polynomial.X (Polynomial.C (v : T))
  have hn' : φ ((Polynomial.C (v : T)) ^ ((p - 1) / 2) *
      Polynomial.X ^ (p - 1)) = 1 := hweight ▸ hn
  simpa only [hweight] using
    weightedSpan φ hp0 Polynomial.X ((Polynomial.C (v : T)) ^ ((p - 1) / 2)) hn'

end SchubertGeometry.DeterminantSection
