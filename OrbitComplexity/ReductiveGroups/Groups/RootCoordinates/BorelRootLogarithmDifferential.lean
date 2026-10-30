import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.LogarithmCoordinateMap
import OrbitComplexity.ReductiveGroups.Groups.Exponential.BorelRootExponentialScaling

/-!
# Borel Root Logarithm Differential

The chosen inverse-exponential coordinates have the expected first-order
behavior on every Ga curve in the Borel Ga-only subgroup. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Pulling back a chosen logarithm coordinate along the Ga
integration of a subgroup tangent gives exactly its linear polynomial. -/
theorem BorelRootLogarithmCoordinate.gaPolynomial
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (f : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range →ₗ[K] K)
    (d : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range) :
    gaPolynomialEquiv K
      (borelRootUnipotentGa J hJ π hπ d.val d.property
        (borelRootLogarithmCoordinate J hJ π hπ f)) =
      Polynomial.C (f d) * Polynomial.X := by
  apply Polynomial.funext
  intro t
  let E := borelRootUnipotentExponentialEquiv J hJ π hπ
  have hcoord := borelRootLogarithmCoordinate_eval J hJ π hπ f (E (t • d))
  rw [E.symm_apply_apply] at hcoord
  change (borelRootUnipotentExponential J hJ π hπ (t • d)).ofConv
      (borelRootLogarithmCoordinate J hJ π hπ f) = f (t • d) at hcoord
  rw [borelRootUnipotentExponential_smul] at hcoord
  rw [gaPolynomialEquiv_eval_point]
  change (gaAffineGroupPoints
    (borelRootUnipotentGa J hJ π hπ d.val d.property)
      (Multiplicative.ofAdd t)).ofConv
    (borelRootLogarithmCoordinate J hJ π hπ f) = _
  simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    LinearMap.map_smul, smul_eq_mul, mul_comm t (f d)] using hcoord

/-- The differential of a chosen logarithm coordinate is precisely
the prescribed linear functional on the original subgroup tangent. -/
theorem borelRootLogarithmCoordinate_tangent
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (f : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range →ₗ[K] K)
    (d : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range) :
    Bialgebra.CounitAlgebra.algEquivSelf K B K
      (d.val (borelRootLogarithmCoordinate J hJ π hπ f)) = f d := by
  have hd := borelRootUnipotentGa_tangent J hJ π hπ d.val d.property
  rw [← hd]
  change Bialgebra.CounitAlgebra.algEquivSelf K B K
    (gaAffineGroupTangent
      (borelRootUnipotentGa J hJ π hπ d.val d.property)
      (borelRootLogarithmCoordinate J hJ π hπ f)) = f d
  rw [gaAffineGroupTangent, gaOriginDerivation_comp_apply,
    BorelRootLogarithmCoordinate.gaPolynomial J hJ π hπ f d]
  simp

/-- Every chosen logarithm coordinate vanishes at the identity.
This is a consequence of the same Ga pullback polynomial. -/
theorem borelRootLogarithmCoordinate_counit
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (f : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range →ₗ[K] K) :
    Coalgebra.counit (R := K) (borelRootLogarithmCoordinate J hJ π hπ f) = 0 := by
  let U := (derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ)).hom).range
  have hpoly := BorelRootLogarithmCoordinate.gaPolynomial J hJ π hπ f (0 : U)
  have hzero := gaPolynomialEquiv_coeff_zero K
    (borelRootUnipotentGa J hJ π hπ (0 : U).val (0 : U).property
      (borelRootLogarithmCoordinate J hJ π hπ f))
  rw [hpoly] at hzero
  rw [CoalgHomClass.counit_comp_apply] at hzero
  simpa using hzero.symm

end ReductiveGroups
