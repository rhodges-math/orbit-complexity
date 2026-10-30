import OrbitComplexity.GroupActions.Rosenlicht.RelativeInvariants
import TauCeti.FieldTheory.Minpoly.IsIntegrallyClosedIn

/-!
# Separable scalar extension of invariant fields

Relative algebraic closedness gives linear disjointness from separable
constants. The invariant field of an irreducible group has the required
relative algebraic closedness in its function field.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v w

/-- A relatively algebraically closed field extension remains a field after
extension of scalars by a separable algebraic extension. -/
theorem tensor_isField_of_separable (k : Type u) [Field k]
    (F : Type v) [Field F] [Algebra k F] (L : Type w) [Field L] [Algebra k L]
    [Algebra.IsSeparable k L] (hF : IsIntegrallyClosedIn k F) :
    IsField (F ⊗[k] L) := by
  apply IntermediateField.LinearDisjoint.isField_of_forall k F L
  intro M _ _ f g
  let _ : Algebra F M := f.toAlgebra
  let _ : Algebra L M := g.toAlgebra
  have : IsScalarTower k F M := IsScalarTower.of_algHom f
  have : IsScalarTower k L M := IsScalarTower.of_algHom g
  have hd := TauCeti.linearDisjoint_fieldRange_of_isIntegrallyClosedIn
    (k := k) (F := F) (E := M) (k' := L) hF
  change g.fieldRange.toSubalgebra.LinearDisjoint f.range at hd
  rw [IntermediateField.linearDisjoint_iff']
  exact hd.symm

namespace Variety

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- The invariant field of an irreducible group is relatively algebraically
closed in the function field. -/
theorem invariantField_integrallyClosed :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    IsIntegrallyClosedIn (invariantField H X) X.scheme.functionField := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  apply isIntegrallyClosedIn_iff.mpr
  refine ⟨(algebraMap (invariantField H X) X.scheme.functionField).injective, ?_⟩
  intro f hf
  exact ⟨⟨f, invariantField_mem_of_isAlgebraic H X f hf.isAlgebraic⟩, rfl⟩


end Variety

end

end GroupActions
