import OrbitComplexity.GroupActions.Varieties.FiniteDimension
import TauCeti.AlgebraicGeometry.Scheme.FunctionField

/-! # Dimension and rational functions

The natural dimension of an irreducible variety equals the finite transcendence degree of
its function field over the base field.

## Main results

* `GroupActions.Variety.natDim_functionField`: dimension equals function-field transcendence
  degree, with the base algebra structure induced by the variety's structure morphism.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions.Variety

universe u

variable {K : Type u} [Field K] (X : GroupActions.Variety K) [IrreducibleSpace X.scheme]

/-- The natural dimension equals the finite transcendence degree of the function field. -/
theorem natDim_functionField :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    X.natDim = (Algebra.trdeg K X.scheme.functionField).toNat := by
  let : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  let : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : LocallyOfFiniteType (X.scheme ↘ Spec (.of K)) := X.locallyOfFiniteType
  have hdim :=
    TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K
      (X := X.scheme)
  change X.dim = _ at hdim
  rw [← X.natDim_cast] at hdim
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp hdim)

end GroupActions.Variety
