import OrbitComplexity.GroupActions.Rosenlicht.BaseFields
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Function fields of birational schemes

An isomorphism between dense open subschemes induces an isomorphism of function fields.
The construction is the composite of the pullbacks along the two open immersions and the
isomorphism between the open subschemes.

## Main definitions

* `birationalFunctionFieldEquiv`: the function-field isomorphism of a partial isomorphism.
* `birationalFunctionFieldAlgEquiv`: the algebra isomorphism of a partial isomorphism
  over an affine base.

-/

namespace GroupActions

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

section Irreducible

variable [IrreducibleSpace X] [IrreducibleSpace Y]

end Irreducible

variable (K : Type u) [CommRing K]
variable [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] [IsIntegral X] [IsIntegral Y]

end

end GroupActions
