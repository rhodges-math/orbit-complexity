import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ModelBaseChange

/-!
# Model Comparison

Presentation-model comparisons respect evaluation in the generic algebra.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

variable {S R K M A ι σ : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (Q : Algebra.Presentation S M ι σ) (e : K ⊗[S] M ≃ₐ[K] A)
    [((Q.baseChange K).ofAlgEquiv e).HasCoeffs R]

/-- The presentation comparison commutes with extension of coefficients on the original model. -/
theorem baseChangeModelEquiv_naturality (hi : Function.Injective (algebraMap R K))
    (x : ((Q.baseChange K).ofAlgEquiv e).ModelOfHasCoeffs R) :
    ((Q.baseChange K).ofAlgEquiv e).tensorModelOfHasCoeffsEquiv R ((1 : K) ⊗ₜ[R] x) =
      e (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M)
        (baseChangeModelEquivOf Q e hi x)) := by
  let P := (Q.baseChange K).ofAlgEquiv e
  let τ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M)
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective x
  change algebraMap K A 1 * MvPolynomial.aeval P.val v =
    e (τ (baseChangeModelEquivOf Q e hi (Ideal.Quotient.mk _ v)))
  rw [map_one, one_mul, baseChangeModelEquivOf_mk]
  have heval : (MvPolynomial.aeval (R := R) P.val).toRingHom =
      e.toRingHom.comp
        (τ.toRingHom.comp (MvPolynomial.aeval (R := R) (Q.baseChange R).val).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change MvPolynomial.aeval (R := R) P.val (MvPolynomial.C r) =
        e (τ (MvPolynomial.aeval (R := R) (Q.baseChange R).val (MvPolynomial.C r)))
      rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
      change algebraMap R A r = e (τ (r ⊗ₜ[S] (1 : M)))
      rw [Algebra.TensorProduct.map_tmul, IsScalarTower.toAlgHom_apply, AlgHom.id_apply]
      change algebraMap R A r = e (algebraMap K (K ⊗[S] M) (algebraMap R K r))
      rw [e.commutes]
      exact IsScalarTower.algebraMap_apply R K A r
    · intro i
      change MvPolynomial.aeval (R := R) P.val (MvPolynomial.X i) =
        e (τ (MvPolynomial.aeval (R := R) (Q.baseChange R).val (MvPolynomial.X i)))
      rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
      simp only [P, Algebra.Presentation.ofAlgEquiv, Algebra.Generators.ofAlgEquiv_val,
        Algebra.Presentation.baseChange, Algebra.Generators.baseChange_val,
        Function.comp_apply]
      change e ((1 : K) ⊗ₜ[S] Q.val i) = e (τ ((1 : R) ⊗ₜ[S] Q.val i))
      simp only [τ, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  exact RingHom.congr_fun heval v

end FrobeniusSplitting
