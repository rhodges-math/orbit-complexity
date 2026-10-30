import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPoints
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaPolynomialCoordinate
import Mathlib.Algebra.Polynomial.Roots

/-!
# Ga Unit Point Determines Morphism

One point of an additive one-parameter subgroup, at parameter
`1`, determines its entire coordinate Hopf morphism in characteristic zero. -/

noncomputable section
namespace ReductiveGroups

variable {K B : Type*} [Field K] [CharZero K] [CommRing B] [HopfAlgebra K B]

/-- Equality of Ga subgroup points at parameter `1` implies equality
at every natural parameter, by the point-group law. -/
theorem gaAffineGroupPoints_eq_natCast_of_eq_one
    (x y : B →ₐc[K] SymmetricAlgebra K K)
    (h : gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) =
      gaAffineGroupPoints y (Multiplicative.ofAdd (1 : K)))
    (n : ℕ) :
    gaAffineGroupPoints x (Multiplicative.ofAdd (n : K)) =
      gaAffineGroupPoints y (Multiplicative.ofAdd (n : K)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn : Multiplicative.ofAdd ((n + 1 : ℕ) : K) =
          Multiplicative.ofAdd (n : K) * Multiplicative.ofAdd (1 : K) := by
        simp [Nat.cast_add]
      rw [hn, map_mul, map_mul, ih, h]

/-- An additive subgroup coordinate morphism is uniquely determined
by its original-group point at parameter `1`. -/
theorem gaAffineGroupPoints_one_injective :
    Function.Injective (fun x : B →ₐc[K] SymmetricAlgebra K K =>
      gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K))) := by
  intro x y h
  ext b
  apply (gaPolynomialEquiv K).injective
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : Set.Infinite (Set.range (fun n : ℕ => (n : K))) :=
    Set.infinite_range_of_injective Nat.cast_injective
  apply hinf.mono
  rintro t ⟨n, rfl⟩
  change Polynomial.eval (n : K) ((gaPolynomialEquiv K) (x b)) =
    Polynomial.eval (n : K) ((gaPolynomialEquiv K) (y b))
  rw [gaPolynomialEquiv_eval_point, gaPolynomialEquiv_eval_point]
  have hn := gaAffineGroupPoints_eq_natCast_of_eq_one x y h n
  have hb := congrArg (fun g : WithConv (B →ₐ[K] K) => g.ofConv b) hn
  simpa [gaAffineGroupPoints, TauCeti.AlgHom.mapDomain_apply_apply] using hb

/-- Consequently the origin tangents also agree. -/
theorem gaAffineGroupTangent_eq_of_points_one_eq
    (x y : B →ₐc[K] SymmetricAlgebra K K)
    (h : gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) =
      gaAffineGroupPoints y (Multiplicative.ofAdd (1 : K))) :
    gaAffineGroupTangent x = gaAffineGroupTangent y := by
  rw [gaAffineGroupPoints_one_injective h]

end ReductiveGroups
