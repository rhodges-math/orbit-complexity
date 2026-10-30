import OrbitComplexity.ReductiveGroups.Groups.Representations.InfinitesimalWordParameters
import OrbitComplexity.ReductiveGroups.Groups.TangentOperators.SquareZeroTangentPoint

/-!
# Infinitesimal Tangent Detection

The full mixed coefficient detects the original tangent vector. -/

noncomputable section
namespace ReductiveGroups
open WithConv

universe u
variable {K B : Type u} [Field K] [CommRing B] [HopfAlgebra K B]

/-- A tangent point at the full word parameter can equal the identity only
when the original tangent vector is zero. No reducedness of the parameter
algebra is required; its full-coefficient functional detects the vector. -/
theorem InfinitesimalTangentDetection.eq_zero_of_fullParameter_point_eq_one
    (n : ℕ) (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (h : squareZeroTangentPoint d (infinitesimalWordParameter K n)
      (infinitesimalWordParameter_sq_zero K n) = 1) : d = 0 := by
  ext b
  have hb := congrArg (fun p : WithConv (B →ₐ[K] InfinitesimalWordParameters K n) =>
    p.ofConv b) h
  rw [squareZeroTangentPoint_apply] at hb
  change algebraMap K (InfinitesimalWordParameters K n) (Coalgebra.counit b) +
    infinitesimalWordParameter K n * algebraMap K (InfinitesimalWordParameters K n)
      (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K (d b)) =
    algebraMap K (InfinitesimalWordParameters K n) (Coalgebra.counit b) at hb
  have hz := add_left_cancel (show
      algebraMap K (InfinitesimalWordParameters K n) (Coalgebra.counit b) +
        infinitesimalWordParameter K n * algebraMap K (InfinitesimalWordParameters K n)
          (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K (d b)) =
      algebraMap K (InfinitesimalWordParameters K n) (Coalgebra.counit b) + 0 by
    simpa only [add_zero] using hb)
  rw [mul_comm, ← Algebra.smul_def] at hz
  have hc := congrArg (infinitesimalWordCoefficient K n) hz
  rw [InfinitesimalWordCoefficient.smul_parameter, map_zero] at hc
  exact (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K).injective
    (hc.trans (map_zero _).symm)

end ReductiveGroups
