import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.GaussPolynomial
import OrbitComplexity.FrobeniusSplitting.Normality.ModelFlat
import Batteries.Tactic.Lint

/-! # Retained squares on simple root charts

The simple-root determinant polynomial is a square. A flat retained
polynomial with that scalar comparison is the same square times its
retained unit, and this identity persists under every specialization.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry ReductiveGroups GroupActions TauCeti
open scoped TensorProduct

namespace SchubertGeometry.DeterminantSection

private theorem polynomial_eq_square {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f)
    (P : Polynomial A) (w : Aˣ)
    (hP : Polynomial.map f P = Polynomial.C (f (w : A)) * Polynomial.X ^ 2) :
    P = Polynomial.C (w : A) * Polynomial.X ^ 2 := by
  apply Polynomial.map_injective f hf
  simpa only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
    using hP

/-- The scalar comparison with the simple-root determinant retains its square
factor and its unit under every specialization of the original flat model. -/
theorem retainedRoot_specialized_square
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) (B : Type u) [CommRing B] [Algebra S B] [Module.Flat S B]
    (e : K ⊗[S] B ≃ₐ[K] K) (P : Polynomial B) (w : Bˣ)
    (hP : Polynomial.map (FrobeniusSplitting.tensorImageHom e).toRingHom P =
      Polynomial.C (FrobeniusSplitting.tensorImageHom e (w : B)) *
        gaPolynomialEquiv K (G.simpleRootMap i
          (HopfAlgebra.rightTranslationAlgHom ((G.reflectionPoint i.val)⁻¹)
            (positiveDetCoefficient G))))
    {T : Type u} [CommRing T] (f : B →+* T) :
    ∃ v : Tˣ, Polynomial.map f P = Polynomial.C (v : T) * Polynomial.X ^ 2 := by
  have hf : Function.Injective (FrobeniusSplitting.tensorImageHom e).toRingHom :=
    FrobeniusSplitting.tensorImageHom_injective e
      (show Function.Injective (algebraMap S K) from Subtype.val_injective)
  have hfield : Polynomial.map (FrobeniusSplitting.tensorImageHom e).toRingHom P =
      Polynomial.C (FrobeniusSplitting.tensorImageHom e (w : B)) * Polynomial.X ^ 2 :=
    hP.trans (congrArg
      (Polynomial.C (FrobeniusSplitting.tensorImageHom e (w : B)) * ·)
      (positiveDet_simple_polynomial G i))
  have hmodel := polynomial_eq_square (FrobeniusSplitting.tensorImageHom e).toRingHom
    hf P w hfield
  refine ⟨Units.map f.toMonoidHom w, ?_⟩
  rw [hmodel, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  rfl

end SchubertGeometry.DeterminantSection
