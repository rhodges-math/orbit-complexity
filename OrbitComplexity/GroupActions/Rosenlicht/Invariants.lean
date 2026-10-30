import OrbitComplexity.GroupActions.Rosenlicht.FieldActions
import OrbitComplexity.GroupActions.Rosenlicht.FixedFields
import TauCeti.AlgebraicGeometry.Scheme.FunctionField

/-!
# Invariant rational functions

Automorphisms of an integral scheme over a field act on its function field by inverse
pullback. The rational functions fixed by that action form an intermediate field.

## Main definitions

* `invariantFunctionField`: the intermediate field of invariant rational functions.

## Main results

* `invariantFunctionField_trdeg_sub`: their transcendence degree is the difference of
  the ambient and relative transcendence degrees.

## Implementation notes

The fixed intermediate field uses `FixedPoints.intermediateField`.
-/

namespace GroupActions

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

variable (K : Type u) [Field K]
variable {X : Scheme.{u}} [X.Over (Spec (.of K))] [IsIntegral X]
variable {M : Type v} [Monoid M]

/-- The intermediate field of rational functions fixed by automorphisms over the base field. -/
def invariantFunctionField (ρ : M →* Aut (X.asOver (Spec (.of K)))) :
    IntermediateField K X.functionField :=
  let σ : M →* Aut X :=
    ((Over.forget (Spec (.of K))).mapAut (X.asOver (Spec (.of K)))).comp ρ
  letI := functionFieldAction σ
  letI := functionFieldAction_smulComm K ρ
  (FixedPoints.intermediateField (F := K) M : IntermediateField K X.functionField)

variable [LocallyOfFiniteType (X ↘ Spec (.of K))]

/-- The natural transcendence degree of invariant rational functions is the ambient degree
minus the relative degree over the invariant field. -/
theorem invariantFunctionField_trdeg_sub
    (ρ : M →* Aut (X.asOver (Spec (.of K)))) :
    (Algebra.trdeg K (invariantFunctionField K ρ)).toNat =
      (Algebra.trdeg K X.functionField).toNat -
        (Algebra.trdeg (invariantFunctionField K ρ) X.functionField).toNat := by
  let σ : M →* Aut X :=
    ((Over.forget (Spec (.of K))).mapAut (X.asOver (Spec (.of K)))).comp ρ
  let _ := functionFieldAction σ
  have : SMulCommClass M K X.functionField := functionFieldAction_smulComm K ρ
  exact fixedField_trdeg_sub (K := K) (M := M) (L := X.functionField)

end

end GroupActions
