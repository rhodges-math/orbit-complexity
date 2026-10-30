import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPoints
import Mathlib.Algebra.Polynomial.Roots

/-!
# Ga Affine Group Point Injectivity

A nonzero tangent makes an additive-group point map injective. -/

noncomputable section
namespace ReductiveGroups

variable {K B : Type*} [Field K] [CharZero K] [CommRing B] [HopfAlgebra K B]

private theorem GaAffineGroupPoints.eq_one_imp_tangent_zero
    (x : B →ₐc[K] SymmetricAlgebra K K) (t : K)
    (ht : gaAffineGroupPoints x (Multiplicative.ofAdd t) = 1)
    (ht0 : t ≠ 0) : gaAffineGroupTangent x = 0 := by
  have hnt : Function.Injective (fun n : ℕ => n • t) := by
    intro m n h
    have h' : (m : K) * t = (n : K) * t := by
      simpa only [nsmul_eq_mul] using h
    exact Nat.cast_injective (mul_right_cancel₀ ht0 h')
  apply Derivation.ext
  intro b
  let p := gaPolynomialEquiv K (x b)
  have hconst : p = Polynomial.C (Coalgebra.counit (R := K) b) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective hnt).mono
    rintro z ⟨n, rfl⟩
    have hpow : gaAffineGroupPoints x (Multiplicative.ofAdd (n • t)) = 1 := by
      change gaAffineGroupPoints x ((Multiplicative.ofAdd t) ^ n) = 1
      rw [map_pow, ht, one_pow]
    change p.eval (n • t) = (Polynomial.C (Coalgebra.counit (R := K) b)).eval (n • t)
    rw [Polynomial.eval_C, gaPolynomialEquiv_eval_point]
    have hb := congrArg (fun f : WithConv (B →ₐ[K] K) => f.ofConv b) hpow
    simpa [gaAffineGroupPoints, TauCeti.AlgHom.mapDomain_apply_apply] using hb
  have hc : p.coeff 1 = 0 := by rw [hconst]; simp
  apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K).injective
  change TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K
    (TauCeti.derivationComp (B := K) x (gaOriginDerivation K) b) = 0
  rw [gaOriginDerivation_comp_apply]
  exact hc

/-- The point map of an additive subgroup is faithful when its origin
tangent is nonzero. -/
theorem GaAffineGroupPoints.injective_of_tangent_ne_zero
    (x : B →ₐc[K] SymmetricAlgebra K K)
    (hx : gaAffineGroupTangent x ≠ 0) :
    Function.Injective (gaAffineGroupPoints x) := by
  apply (injective_iff_map_eq_one (gaAffineGroupPoints x)).2
  intro t ht
  by_contra hne
  have ht0 : Multiplicative.toAdd t ≠ (0 : K) := by
    intro h
    apply hne
    simpa using congrArg Multiplicative.ofAdd h
  have := GaAffineGroupPoints.eq_one_imp_tangent_zero x (Multiplicative.toAdd t)
    (by simpa using ht) ht0
  exact hx this

end ReductiveGroups
