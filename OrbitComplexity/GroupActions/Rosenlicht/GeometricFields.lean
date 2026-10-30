import OrbitComplexity.GroupActions.Rosenlicht.SeparableConstants
import OrbitComplexity.GroupActions.Rosenlicht.EssentialTensors
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Geometric integrality of invariant field extensions

In characteristic zero a relatively algebraically closed, finitely generated
field extension remains integral after every field extension of the base.
Algebraic closure first makes the constants algebraically closed, and flatness
then descends integrality to the specified extension.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v w

/-- A relatively algebraically closed field extension essentially of finite type
in characteristic zero stays integral after every scalar field extension. -/
theorem tensor_isDomain_of_integrallyClosed (k : Type u) [Field k] [CharZero k]
    (F : Type v) [Field F] [Algebra k F] [Algebra.EssFiniteType k F]
    (L : Type w) [Field L] [Algebra k L] (hF : IsIntegrallyClosedIn k F) :
    IsDomain (F ⊗[k] L) := by
  let Ω := AlgebraicClosure k
  let M := AlgebraicClosure L
  let g : Ω →ₐ[k] M := IsAlgClosed.lift
  let _ : Algebra Ω M := g.toAlgebra
  have : IsScalarTower k Ω M := IsScalarTower.of_algHom g
  let T := Ω ⊗[k] F
  have hT : IsField T := (Algebra.TensorProduct.comm k Ω F).toMulEquiv.isField
    (tensor_isField_of_separable k F Ω hF)
  let _ : Field T := hT.toField
  have : Algebra.EssFiniteType Ω T := Algebra.EssFiniteType.baseChange k F Ω
  have : IsDomain (T ⊗[Ω] M) := tensorField_isDomain Ω T M
  have : IsDomain (M ⊗[Ω] T) :=
    (Algebra.TensorProduct.comm Ω M T).toMulEquiv.isDomain
  have : IsDomain (M ⊗[k] F) :=
    (Algebra.TensorProduct.cancelBaseChange k Ω Ω M F).symm.toMulEquiv.isDomain
  have : IsDomain (F ⊗[k] M) :=
    (Algebra.TensorProduct.comm k F M).toMulEquiv.isDomain
  let j : F ⊗[k] L →ₐ[k] F ⊗[k] M :=
    Algebra.TensorProduct.map (AlgHom.id k F) (IsScalarTower.toAlgHom k L M)
  have hj : Function.Injective j :=
    Module.Flat.lTensor_preserves_injective_linearMap
      (IsScalarTower.toAlgHom k L M).toLinearMap (algebraMap L M).injective
  exact Function.Injective.isDomain j hj

namespace Variety

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
variable (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- The function field over the invariant field of an irreducible group stays
integral after any field extension of the invariant field. -/
theorem invariantField_baseChange_domain :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    ∀ (L : Type v) [Field L] [Algebra (invariantField H X) L],
      IsDomain (X.scheme.functionField ⊗[invariantField H X] L) := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let E := invariantField H X
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have : LocallyOfFiniteType (X.scheme ↘ Spec (.of K)) := X.locallyOfFiniteType
  have : Algebra.EssFiniteType E X.scheme.functionField :=
    Algebra.EssFiniteType.of_comp K E X.scheme.functionField
  intro L _ _
  exact tensor_isDomain_of_integrallyClosed E X.scheme.functionField L
    (invariantField_integrallyClosed H X)

end Variety

end

end GroupActions
