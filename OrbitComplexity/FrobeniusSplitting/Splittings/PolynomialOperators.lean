import OrbitComplexity.FrobeniusSplitting.Splittings.LinearTensorProduct
import OrbitComplexity.FrobeniusSplitting.Normality.TensorCoordinates
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorTransport
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorNormalization
import OrbitComplexity.FrobeniusSplitting.Splittings.CartierCoordinates

/-! # Polynomial Cartier traces with nonnormalized coefficient operators -/

namespace FrobeniusSplitting
open scoped TensorProduct
noncomputable section
variable {K A : Type*} {p : ℕ} [Field K] [ExpChar K p] [PerfectRing K p]
  [CommRing A] [Algebra K A]

/-- Tensoring with the perfect-field trace defines the polynomial coefficient operator. -/
def polynomialTraceOfOperator (ψ : FrobeniusLinearMap A p) :
    FrobeniusLinearMap (Polynomial A) p :=
  (FrobeniusLinearMap.tensorProduct (K := K) ψ
    (univariateTrace (RingSplitting.ofPerfectRing K p))).transport
      (polynomialTensorEquiv K A).toRingEquiv

private theorem coefficient_scalar (ψ : FrobeniusLinearMap A p) (a : A) (r : K) :
    ψ (a * algebraMap K A r) =
      ψ a * algebraMap K A ((RingSplitting.ofPerfectRing K p) r) := by
  have hr : (algebraMap K A ((frobeniusEquiv K p).symm r)) ^ p = algebraMap K A r := by
    rw [← map_pow]
    exact congrArg (algebraMap K A) ((frobeniusEquiv K p).apply_symm_apply r)
  change ψ (a * algebraMap K A r) = ψ a * algebraMap K A ((frobeniusEquiv K p).symm r)
  rw [← hr, mul_comm a _, ψ.map_pow_mul, mul_comm]

private theorem tensor_trace_coeff (ψ : FrobeniusLinearMap A p)
    (z : A ⊗[K] Polynomial K) (n : ℕ) :
    ((polynomialTensorEquiv K A)
      (FrobeniusLinearMap.tensorProduct ψ
        (univariateTrace (RingSplitting.ofPerfectRing K p)) z)).coeff n =
      ψ (((polynomialTensorEquiv K A) z).coeff (p * n + (p - 1))) := by
  induction z using TensorProduct.inductionOn with
  | tmul a f =>
    rw [FrobeniusLinearMap.tensorProduct_tmul, polynomialTensorEquiv_tmul,
      polynomialTensorEquiv_tmul]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map, univariateTrace_coeff]
    exact (coefficient_scalar ψ a (f.coeff (p * n + (p - 1)))).symm
  | add x y hx hy =>
    simp only [map_add, Polynomial.coeff_add, hx, hy]

/-- The polynomial trace applies its coefficient operator in degrees congruent to minus one. -/
theorem polynomialTraceOfOperator_coeff (ψ : FrobeniusLinearMap A p)
    (f : Polynomial A) (n : ℕ) :
    (polynomialTraceOfOperator (K := K) ψ f).coeff n =
      ψ (f.coeff (p * n + (p - 1))) := by
  change ((polynomialTensorEquiv K A)
    (FrobeniusLinearMap.tensorProduct ψ (univariateTrace (RingSplitting.ofPerfectRing K p))
      ((polynomialTensorEquiv K A).symm f))).coeff n = _
  simpa only [AlgEquiv.apply_symm_apply] using
    tensor_trace_coeff ψ ((polynomialTensorEquiv K A).symm f) n

/-- For a normalized coefficient operator the tensor trace is the existing Cartier trace. -/
theorem polynomialTraceOfOperator_normalized [ExpChar A p] (base : RingSplitting A p) :
    polynomialTraceOfOperator (K := K) base.toOperator = univariateTrace base := by
  apply FrobeniusLinearMap.ext
  intro f
  ext n
  rw [polynomialTraceOfOperator_coeff, univariateTrace_coeff]
  rfl

end
end FrobeniusSplitting
