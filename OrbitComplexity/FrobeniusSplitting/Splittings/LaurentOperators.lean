import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialOperators

/-! # Laurent traces with nonnormalized coefficient operators -/

namespace FrobeniusSplitting
open scoped TensorProduct
noncomputable section
variable {K A : Type*} {p : ℕ} [Field K] [ExpChar K p] [PerfectRing K p]
  [CommRing A] [Algebra K A]

/-- Tensoring with perfect-field Laurent trace extends the coefficient operator. -/
def laurentTraceOfOperator (ψ : FrobeniusLinearMap A p) :
    FrobeniusLinearMap (LaurentPolynomial A) p :=
  (FrobeniusLinearMap.tensorProduct (K := K) ψ
    (laurentTrace (RingSplitting.ofPerfectRing K p))).transport
      (AddMonoidAlgebra.scalarTensorEquiv K A).toRingEquiv

private theorem coefficient_scalar (ψ : FrobeniusLinearMap A p) (a : A) (r : K) :
    ψ (a * algebraMap K A r) =
      ψ a * algebraMap K A ((RingSplitting.ofPerfectRing K p) r) := by
  have hr : (algebraMap K A ((frobeniusEquiv K p).symm r)) ^ p = algebraMap K A r := by
    rw [← map_pow]
    exact congrArg (algebraMap K A) ((frobeniusEquiv K p).apply_symm_apply r)
  change ψ (a * algebraMap K A r) = ψ a * algebraMap K A ((frobeniusEquiv K p).symm r)
  rw [← hr, mul_comm a _, ψ.map_pow_mul, mul_comm]

private theorem tensor_coefficient (a : A) (f : LaurentPolynomial K) (n : ℤ) :
    (AddMonoidAlgebra.scalarTensorEquiv K A (a ⊗ₜ[K] f)).coeff n =
      a * algebraMap K A (f.coeff n) := by
  rw [AddMonoidAlgebra.scalarTensorEquiv_tmul]
  rfl

private theorem tensor_trace_coeff (ψ : FrobeniusLinearMap A p)
    (z : A ⊗[K] LaurentPolynomial K) (n : ℤ) :
    ((AddMonoidAlgebra.scalarTensorEquiv K A)
      (FrobeniusLinearMap.tensorProduct ψ
        (laurentTrace (RingSplitting.ofPerfectRing K p)) z)).coeff n =
      ψ (((AddMonoidAlgebra.scalarTensorEquiv K A) z).coeff (p • n + (p - 1))) := by
  induction z using TensorProduct.inductionOn with
  | tmul a f =>
    rw [FrobeniusLinearMap.tensorProduct_tmul, tensor_coefficient, tensor_coefficient,
      laurentTrace_coeff]
    exact (coefficient_scalar ψ a (f.coeff (p • n + (p - 1)))).symm
  | add x y hx hy =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]

/-- The Laurent trace extracts shifted characteristic multiples through its coefficient operator. -/
theorem laurentTraceOfOperator_coeff (ψ : FrobeniusLinearMap A p)
    (f : LaurentPolynomial A) (n : ℤ) :
    (laurentTraceOfOperator (K := K) ψ f).coeff n = ψ (f.coeff (p • n + (p - 1))) := by
  change ((AddMonoidAlgebra.scalarTensorEquiv K A)
    (FrobeniusLinearMap.tensorProduct ψ (laurentTrace (RingSplitting.ofPerfectRing K p))
      ((AddMonoidAlgebra.scalarTensorEquiv K A).symm f))).coeff n = _
  simpa only [AlgEquiv.apply_symm_apply] using
    tensor_trace_coeff ψ ((AddMonoidAlgebra.scalarTensorEquiv K A).symm f) n

/-- Reciprocal coordinates transform the trace by the twice-top monomial. -/
theorem laurentOperator_invert (ψ : FrobeniusLinearMap A p) (f : LaurentPolynomial A) :
    laurentTraceOfOperator (K := K) ψ
        (LaurentPolynomial.T (2 * (p - 1)) * LaurentPolynomial.invert f) =
      LaurentPolynomial.invert (laurentTraceOfOperator (K := K) ψ f) := by
  ext n
  rw [laurentTraceOfOperator_coeff, LaurentPolynomial.invert_apply,
    laurentTraceOfOperator_coeff]
  change ψ ((AddMonoidAlgebra.single (2 * ((p : ℤ) - 1)) (1 : A) *
    LaurentPolynomial.invert f).coeff (p • n + (p - 1))) = _
  rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, LaurentPolynomial.invert_apply]
  congr 2
  simp only [smul_neg]
  ring

private theorem coefficient_nat (f : Polynomial A) (n : ℕ) :
    f.toLaurent.coeff (n : ℤ) = f.coeff n := by
  change (Finsupp.mapDomain (fun n : ℕ ↦ (n : ℤ)) f.toFinsupp.coeff) (n : ℤ) = f.coeff n
  rw [Finsupp.mapDomain_apply_of_injective Nat.cast_injective]
  rfl

private theorem coefficient_neg (f : Polynomial A) (n : ℤ) (hn : n < 0) :
    f.toLaurent.coeff n = 0 := by
  change (Finsupp.mapDomain (fun n : ℕ ↦ (n : ℤ)) f.toFinsupp.coeff) n = 0
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨m, hm⟩
  rw [← hm] at hn
  exact (not_lt_of_ge (Int.natCast_nonneg m)) hn

/-- Polynomial inclusion into the Laurent ring preserves the coefficient trace. -/
theorem laurentOperator_toLaurent (ψ : FrobeniusLinearMap A p) (f : Polynomial A) :
    laurentTraceOfOperator (K := K) ψ f.toLaurent =
      (polynomialTraceOfOperator (K := K) ψ f).toLaurent := by
  ext n
  cases n with
  | ofNat n =>
    rw [laurentTraceOfOperator_coeff]
    change ψ (f.toLaurent.coeff (p • (n : ℤ) + ((p : ℤ) - 1))) =
      (polynomialTraceOfOperator (K := K) ψ f).toLaurent.coeff (n : ℤ)
    have hp : 1 ≤ p := expChar_pos K p
    have hcast : p • (n : ℤ) + ((p : ℤ) - 1) = ((p * n + (p - 1) : ℕ) : ℤ) := by
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp, Nat.cast_one]
    rw [hcast, coefficient_nat, coefficient_nat, polynomialTraceOfOperator_coeff]
  | negSucc n =>
    have hneg : p • Int.negSucc n + ((p : ℤ) - 1) < 0 := by
      have hle : Int.negSucc n ≤ -1 := by omega
      have hmul := mul_le_mul_of_nonneg_left hle (Int.natCast_nonneg p)
      simp only [mul_neg_one] at hmul
      change (p : ℤ) * Int.negSucc n + ((p : ℤ) - 1) < 0
      omega
    rw [laurentTraceOfOperator_coeff, coefficient_neg f _ hneg,
      coefficient_neg (polynomialTraceOfOperator (K := K) ψ f) _ (Int.negSucc_lt_zero n),
      ψ.map_zero]

end
end FrobeniusSplitting
