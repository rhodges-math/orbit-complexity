import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPoints
import OrbitComplexity.ReductiveGroups.Groups.Tangents.FiniteTypeAffineGroupDifferential
import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupAdjointMatrix
import OrbitComplexity.ReductiveGroups.Groups.Representations.AdjointRepresentation
import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# Ga Affine Group Conjugation

Conjugation of additive subgroups follows from their tangent vectors.
In particular an adjoint weight equation gives the exact parameter scaling. -/

noncomputable section
namespace ReductiveGroups

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem associativeExponential_units_conjugate
    {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]
    (u : Aˣ) (X : A) (hX : IsNilpotent X) :
    associativeExponential (K := K) ((u : A) * X * (u⁻¹ : Aˣ)) =
      (u : A) * associativeExponential (K := K) X * (u⁻¹ : Aˣ) := by
  let : Algebra ℚ K := (Rat.castHom K).toAlgebra
  let : Module ℚ A := Module.compHom A (algebraMap ℚ K)
  exact IsNilpotent.exp_smul (ConjAct.toConjAct u) hX

variable {K B : Type*} [Field K] [CharZero K] [CommRing B]
  [HopfAlgebra K B] [Algebra.FiniteType K B]

/-- An adjoint equation on subgroup tangents determines conjugation
of their points, with the same scalar on the additive parameter. -/
theorem GaAffineGroupPoints.conjugate_of_tangent_eq
    (x y : B →ₐc[K] SymmetricAlgebra K K)
    (g : WithConv (B →ₐ[K] K)) (c : K)
    (h : affineGroupAdjointRepresentation g (gaAffineGroupTangent x) =
      c • gaAffineGroupTangent y) (t : K) :
    g * gaAffineGroupPoints x (Multiplicative.ofAdd t) * g⁻¹ =
      gaAffineGroupPoints y (Multiplicative.ofAdd (c * t)) := by
  obtain ⟨n, ρ, hρ, _⟩ :=
    FiniteTypeAffineGroup.exists_injective_matrixDifferential (K := K) (B := B)
  let G := TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ g)
  let X := affineGroupMatrixDifferential n ρ (gaAffineGroupTangent x)
  let Y := affineGroupMatrixDifferential n ρ (gaAffineGroupTangent y)
  have hXY : (G : Matrix (Fin n) (Fin n) K) * X * (G⁻¹ :
      Matrix.GeneralLinearGroup (Fin n) K) = c • Y := by
    have he := congrArg (affineGroupMatrixDifferential n ρ) h
    have hs := (affineGroupMatrixDifferential n ρ).toLinearMap.map_smul c
      (gaAffineGroupTangent y)
    simpa only [G, X, Y, LieHom.coe_toLinearMap, affineGroupAdjointRepresentation_apply,
      affineGroupMatrixDifferential_adjoint] using he.trans hs
  have hscaled : (G : Matrix (Fin n) (Fin n) K) * (t • X) *
      (G⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) = (c * t) • Y := by
    rw [mul_smul_comm, smul_mul_assoc, hXY, smul_smul, mul_comm t c]
  have hmatrix : (G : Matrix (Fin n) (Fin n) K) *
      associativeExponential (K := K) (t • X) *
        (G⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) =
      associativeExponential (K := K) ((c * t) • Y) := by
    rw [← associativeExponential_units_conjugate G (t • X)
      ((gaAffineGroupTangent_matrix_nilpotent n x ρ).smul t), hscaled]
  have hgl :
      TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ
        (g * gaAffineGroupPoints x (Multiplicative.ofAdd t) * g⁻¹)) =
      TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ
        (gaAffineGroupPoints y (Multiplicative.ofAdd (c * t)))) := by
    apply Units.ext
    simpa only [map_mul, map_inv, Units.val_mul, GaAffineGroupPoints.matrix_eq_exponential,
      G, X, Y] using hmatrix
  have hpoints := (TauCeti.GeneralLinear.pointsMulEquiv n).injective hgl
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro b
  obtain ⟨a, rfl⟩ := hρ b
  have ha := congrArg (fun z : WithConv
    (TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] K) => z.ofConv a) hpoints
  simpa only [TauCeti.AlgHom.mapDomain_apply_apply] using ha

/-- An adjoint eigenvector equation gives normalization of the corresponding
additive subgroup, coefficient by coefficient in its parameter. -/
theorem gaAffineGroupPoints_conjugate_of_weight
    (x : B →ₐc[K] SymmetricAlgebra K K)
    (g : WithConv (B →ₐ[K] K)) (c : K)
    (h : affineGroupAdjointRepresentation g (gaAffineGroupTangent x) =
      c • gaAffineGroupTangent x) (t : K) :
    g * gaAffineGroupPoints x (Multiplicative.ofAdd t) * g⁻¹ =
      gaAffineGroupPoints x (Multiplicative.ofAdd (c * t)) :=
  GaAffineGroupPoints.conjugate_of_tangent_eq x x g c h t

end ReductiveGroups
