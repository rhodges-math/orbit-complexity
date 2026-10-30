import OrbitComplexity.GroupActions.Actions.ActionMap
import OrbitComplexity.GroupActions.Varieties.Noetherian
import OrbitComplexity.GroupActions.Rosenlicht.IntegralProducts
import OrbitComplexity.GroupActions.Rosenlicht.BaseFields

/-!
# Rational pullback of an algebraic action

An integral group acting on an integral variety has an integral product
with that variety. The action morphism is dominant, so its pullback gives a map
from the variety's function field to the function field of the product.

## Main results

* `Variety.product_integral`: products of integral varieties are integral.

## Main definitions

-/

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- The product of integral varieties over an algebraically closed field is integral. -/
theorem product_integral : IsIntegral (H.toOver ⊗ X.toOver).left := by
  have : IsIntegral H.scheme := isIntegral_of_irreducibleSpace_of_isReduced H.scheme
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  change IsIntegral (Limits.pullback H.toSpec X.toSpec)
  exact isIntegral_pullback_over_field H.toSpec X.toSpec

variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]

end

end GroupActions.Variety
