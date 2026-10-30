import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaPolynomialCoordinate
import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap

/-!
# Ga Tangent Coordinate

The coordinate derivative at zero is the counit-valued tangent
derivation of the additive group, and is coefficient extraction at degree one. -/

noncomputable section
namespace ReductiveGroups

variable (K : Type*) [Field K]

/-- The equality is

```lean
(gaPolynomialEquiv K a).coeff 0 = Coalgebra.counit (R := K) a
```
-/
theorem gaPolynomialEquiv_coeff_zero (a : SymmetricAlgebra K K) :
    (gaPolynomialEquiv K a).coeff 0 = Coalgebra.counit (R := K) a := by
  rw [Polynomial.coeff_zero_eq_eval_zero, gaPolynomialEquiv_eval_point]
  change ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (1 : Multiplicative K)).ofConv a = _
  rw [map_one]
  simp

/-- The tangent vector d/dt at the identity of the additive group. -/
def gaOriginDerivation :
    Derivation K (SymmetricAlgebra K K)
      (TauCeti.Bialgebra.CounitAlgebra K (SymmetricAlgebra K K) K) where
  toFun a := (gaPolynomialEquiv K a).coeff 1
  map_add' a b := by
    change (gaPolynomialEquiv K (a + b)).coeff 1 =
      (gaPolynomialEquiv K a).coeff 1 + (gaPolynomialEquiv K b).coeff 1
    simp
  map_smul' r a := by
    change (gaPolynomialEquiv K (r • a)).coeff 1 = r * _
    simp
  map_one_eq_zero' := by
    change ((gaPolynomialEquiv K 1).coeff 1 : K) = (0 : K)
    rw [map_one (gaPolynomialEquiv K), Polynomial.coeff_one]
    simp
  leibniz' a b := by
    apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K
      (SymmetricAlgebra K K) K).injective
    rw [map_add, TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul,
      TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul]
    change (gaPolynomialEquiv K (a * b)).coeff 1 =
      Coalgebra.counit (R := K) a * (gaPolynomialEquiv K b).coeff 1 +
        Coalgebra.counit (R := K) b * (gaPolynomialEquiv K a).coeff 1
    rw [map_mul, Polynomial.mul_coeff_one,
      gaPolynomialEquiv_coeff_zero, gaPolynomialEquiv_coeff_zero]
    rw [mul_comm ((gaPolynomialEquiv K a).coeff 1)]

/-- The equality is

```lean
TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K (SymmetricAlgebra K K) K
      (gaOriginDerivation K a) = (gaPolynomialEquiv K a).coeff 1
```
-/
@[simp]
theorem gaOriginDerivation_apply (a : SymmetricAlgebra K K) :
    TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K (SymmetricAlgebra K K) K
      (gaOriginDerivation K a) = (gaPolynomialEquiv K a).coeff 1 := rfl

/-- The equality is

```lean
TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K (SymmetricAlgebra K K) K
      (gaOriginDerivation K (SymmetricAlgebra.ι K K 1)) = 1
```
-/
theorem gaOriginDerivation_generator :
    TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K (SymmetricAlgebra K K) K
      (gaOriginDerivation K (SymmetricAlgebra.ι K K 1)) = 1 := by
  rw [gaOriginDerivation_apply, gaPolynomialEquiv_generator, Polynomial.coeff_X_one]

/-- The differential of a coordinate bialgebra map on the additive
group's unit tangent extracts the degree-one coefficient of its pullback. -/
theorem gaOriginDerivation_comp_apply
    {B : Type*} [CommRing B] [Bialgebra K B]
    (φ : B →ₐc[K] SymmetricAlgebra K K) (a : B) :
    TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K
      (TauCeti.derivationComp (B := K) φ (gaOriginDerivation K) a) =
      (gaPolynomialEquiv K (φ a)).coeff 1 := by
  rw [TauCeti.algEquivSelf_derivationComp_apply, gaOriginDerivation_apply]
  rfl

end ReductiveGroups
