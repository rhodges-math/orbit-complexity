import OrbitComplexity.FrobeniusSplitting.Splittings.CartierCoordinates
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorMorphisms
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorTransport

/-! # The sign of the reciprocal-coordinate Cartier factor -/

open AlgebraicGeometry CategoryTheory
noncomputable section

namespace FrobeniusSplitting

universe u

variable (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]

private theorem reciprocal_sign : (-1 : C) ^ (p - 1) = 1 := by
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel (expChar_pos C p)
  have hn : (-1 : C) ^ p = -1 := by
    have h := (frobenius C p).map_neg (1 : C)
    change (-1 : C) ^ p = -((1 : C) ^ p) at h
    simpa only [one_pow] using h
  calc
    (-1 : C) ^ (p - 1) = ((-1 : C) ^ (p - 1) * (-1)) * (-1) := by ring
    _ = (-1 : C) ^ p * (-1) := by rw [← pow_succ, hp]
    _ = 1 := by rw [hn]; ring

private theorem laurentTrace_jacobian (base : RingSplitting C p)
    (f : LaurentPolynomial C) :
    laurentTrace base
        (LaurentPolynomial.C ((-1 : C) ^ (p - 1)) *
          LaurentPolynomial.T (2 * ((p : ℤ) - 1)) * LaurentPolynomial.invert f) =
      LaurentPolynomial.invert (laurentTrace base f) := by
  rw [reciprocal_sign C p, map_one, one_mul]
  exact laurentTrace_invert base f

/-- Polynomial and Laurent traces commute with the chart inclusion on every open. -/
theorem traceOverlap_toLaurent (base : RingSplitting C p)
    (U : (Spec (.of (Polynomial C))).Opens) (m : Γ(Spec (.of (Polynomial C)), U)) :
    ((laurentTrace base).toSpec (expChar_pos C p)).onOpen
        ((Spec.map (CommRingCat.ofHom Polynomial.toLaurent)) ⁻¹ᵁ U)
        ((Spec.map (CommRingCat.ofHom Polynomial.toLaurent)).app U m) =
      (Spec.map (CommRingCat.ofHom Polynomial.toLaurent)).app U
        (((univariateTrace base).toSpec (expChar_pos C p)).onOpen U m) :=
  (univariateTrace base).toSpec_naturality (laurentTrace base) (expChar_pos C p)
    Polynomial.toLaurent (laurentTrace_toLaurent base) U m

private def reciprocalMap : Spec (.of (LaurentPolynomial C)) ⟶
    Spec (.of (LaurentPolynomial C)) :=
  Spec.map (CommRingCat.ofHom
    (LaurentPolynomial.invert : LaurentPolynomial C ≃ₐ[C] LaurentPolynomial C).toRingHom)

private def reciprocalTrace (base : RingSplitting C p) :
    FrobeniusLinearMap (LaurentPolynomial C) p :=
  (laurentTrace base).weight
    (LaurentPolynomial.C ((-1 : C) ^ (p - 1)) *
      LaurentPolynomial.T (2 * ((p : ℤ) - 1)))

private theorem reciprocalTrace_commute (base : RingSplitting C p)
    (f : LaurentPolynomial C) :
    reciprocalTrace C p base (LaurentPolynomial.invert f) =
      LaurentPolynomial.invert (laurentTrace base f) := laurentTrace_jacobian C p base f

/-- Reciprocal Laurent coordinates satisfy the signed trace law on every open. -/
theorem traceOverlap_reciprocal (base : RingSplitting C p)
    (U : (Spec (.of (LaurentPolynomial C))).Opens)
    (m : Γ(Spec (.of (LaurentPolynomial C)), U)) :
    ((reciprocalTrace C p base).toSpec (expChar_pos C p)).onOpen
        ((reciprocalMap C) ⁻¹ᵁ U)
        ((reciprocalMap C).app U m) =
      (reciprocalMap C).app U
        (((laurentTrace base).toSpec (expChar_pos C p)).onOpen U m) :=
  (laurentTrace base).toSpec_naturality (reciprocalTrace C p base)
    (expChar_pos C p)
    (LaurentPolynomial.invert : LaurentPolynomial C ≃ₐ[C] LaurentPolynomial C).toRingHom
    (reciprocalTrace_commute C p base) U m

end FrobeniusSplitting
