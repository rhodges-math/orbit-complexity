import OrbitComplexity.GroupActions.Rosenlicht.GenericFieldFibres
import Mathlib.FieldTheory.LinearDisjoint

/-!
# Algebraic elements over invariant fields

An integral self-tensor product forces algebraic elements to lie in the base
field. Applied to the invariant field of an irreducible algebraic group, this
shows that the invariant field is algebraically closed in the function field.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

open scoped TensorProduct

universe u v w

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]

/-- If the self-tensor product over an intermediate field is integral, every
algebraic element over that intermediate field already belongs to it. -/
theorem mem_of_tensorDomain (E : IntermediateField K F) [IsDomain (F ⊗[E] F)]
    {f : F} (hf : IsAlgebraic E f) : f ∈ E := by
  let L := IntermediateField.adjoin E ({f} : Set F)
  let j : F ⊗[E] L →ₐ[E] F ⊗[E] F :=
    Algebra.TensorProduct.map (AlgHom.id E F) L.val
  have hj : Function.Injective j :=
    Module.Flat.lTensor_preserves_injective_linearMap L.val.toLinearMap Subtype.val_injective
  have : IsDomain (F ⊗[E] L) := Function.Injective.isDomain j hj
  have hL : Algebra.IsAlgebraic E L := IntermediateField.isAlgebraic_adjoin_simple hf.isIntegral
  have hfield : IsField (F ⊗[E] L) :=
    Algebra.TensorProduct.isField_of_isAlgebraic E F L (Or.inr hL)
  let _ : Field (F ⊗[E] L) := hfield.toField
  let μ : F ⊗[E] L →ₐ[E] F := Algebra.TensorProduct.lift (AlgHom.id E F) L.val
    (fun _ _ ↦ Commute.all _ _)
  let fL : L := ⟨f, IntermediateField.subset_adjoin E {f} (Set.mem_singleton f)⟩
  have he : f ⊗ₜ[E] (1 : L) = (1 : F) ⊗ₜ[E] fL := by
    apply μ.toRingHom.injective
    simp [μ, fL]
  apply (tensor_eq_iff_mem E f).mp
  have he' := congrArg j he
  change f ⊗ₜ[E] (1 : F) = (1 : F) ⊗ₜ[E] f at he'
  exact he'

namespace Variety

variable [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- A function algebraic over the invariant field of an irreducible group
is invariant. -/
theorem invariantField_mem_of_isAlgebraic (f : X.scheme.functionField) :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    IsAlgebraic (invariantField H X) f → f ∈ invariantField H X := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have := invariantFieldTensor_isDomain H X
  exact mem_of_tensorDomain (invariantField H X)

end Variety

end

end GroupActions
