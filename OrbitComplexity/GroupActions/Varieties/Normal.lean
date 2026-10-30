import OrbitComplexity.GroupActions.Varieties.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Normal varieties

A variety is normal when each stalk of its structure sheaf is an integrally closed domain.

## Main definitions

* `GroupActions.Variety.IsNormal`: stalkwise normality of a variety.
-/

open AlgebraicGeometry

namespace GroupActions.Variety

universe u

variable {K : Type u} [Field K]

/-- A variety is normal if every stalk is an integrally closed domain. -/
def IsNormal (X : GroupActions.Variety K) : Prop :=
  ∀ x : X.scheme, IsDomain (X.scheme.presheaf.stalk x) ∧
    IsIntegrallyClosed (X.scheme.presheaf.stalk x)

end GroupActions.Variety
