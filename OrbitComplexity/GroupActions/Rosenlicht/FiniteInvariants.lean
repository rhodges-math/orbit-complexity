import OrbitComplexity.GroupActions.Rosenlicht.InvariantDescent
import OrbitComplexity.GroupActions.Rosenlicht.GenericOrbit

/-!
# Finite generation of invariant rational functions

The function field of an integral scheme locally of finite type is a finitely
generated field extension. Its field of invariant rational functions is therefore
finitely generated, both for an action by scheme automorphisms and for an
algebraic group action on a variety.

## Main results

* `invariantFunctionField_essFiniteType`: finite generation for scheme automorphisms.
* `Variety.invariantField_essFiniteType`: finite generation for algebraic group actions.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u v

variable (K : Type u) [Field K]
variable {X : Scheme.{u}} [X.Over (Spec (.of K))] [IsIntegral X]
variable [LocallyOfFiniteType (X ↘ Spec (.of K))]
variable {G : Type v} [Group G]

/-- Invariant rational functions under scheme automorphisms form a finitely
generated field extension of the base field. -/
theorem invariantFunctionField_essFiniteType
    (ρ : G →* Aut (X.asOver (Spec (.of K)))) :
    Algebra.EssFiniteType K (invariantFunctionField K ρ) := by
  let σ : G →* Aut X :=
    ((Over.forget (Spec (.of K))).mapAut (X.asOver (Spec (.of K)))).comp ρ
  let _ := functionFieldAction σ
  have : SMulCommClass G K X.functionField := functionFieldAction_smulComm K ρ
  exact fixedField_essFiniteType (K := K) (F := X.functionField) (G := G)

namespace Variety

variable {K} (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [IrreducibleSpace X.scheme]

/-- The invariant rational functions of an algebraic group action on an
irreducible variety form a finitely generated field extension. -/
theorem invariantField_essFiniteType :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    Algebra.EssFiniteType K (invariantField H X) := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : LocallyOfFiniteType (X.scheme ↘ Spec (.of K)) := X.locallyOfFiniteType
  exact invariantFunctionField_essFiniteType K (translationHom H X)

end Variety

end

end GroupActions
