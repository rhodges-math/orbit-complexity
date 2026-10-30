/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

The matrix-conjugation proof below is adapted from
TauCeti/Algebra/AlgebraicGroup/GeneralLinear/Adjoint/Basic.lean at
ff4727b73ce4a7f24e496b141778838be685f1b5.
-/

import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
import TauCeti.Algebra.AlgebraicGroup.Tangent.Adjoint
import TauCeti.Algebra.AlgebraicGroup.Tangent.CounitPoints

/-!
# General Linear Adjoint Matrix

The adjoint action on the tangent matrix of `GLₙ`. -/

noncomputable section
namespace ReductiveGroups

open WithConv TauCeti.GeneralLinear

variable {K B : Type*} [CommRing K] [CommRing B] [Algebra K B]
variable (n : ℕ)

/-- Convert a counit-algebra-valued `GLₙ` point to its invertible matrix. -/
def generalLinearCounitPointsMulEquiv :
    WithConv (TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐ[K]
      TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) B) ≃*
      Matrix.GeneralLinearGroup (Fin n) B :=
  (TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K
    (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) B).trans
      (TauCeti.GeneralLinear.pointsMulEquiv (R := K) (A := B) n)

variable
  (g : WithConv (TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐ[K]
    TauCeti.Bialgebra.CounitAlgebra K
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) B))
  (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
    (TauCeti.Bialgebra.CounitAlgebra K
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) B))

private theorem GeneralLinearCounitPointsMulEquiv.eq_pointsMulEquiv :
    generalLinearCounitPointsMulEquiv n g =
      TauCeti.GeneralLinear.pointsMulEquiv n
        (TauCeti.AlgHom.mapValue
          (H := TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
          (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K
            (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) B).toAlgHom g) := by
  rw [← TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv_eq_mapValue]
  exact MulEquiv.trans_apply _ _ _

/-- The equality is

```lean
generalLinearCounitPointsMulEquiv n g i j =
      TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) B
        (g.ofConv (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
          (TauCeti.GeneralLinear.coordinateRingMap K n (MvPolynomial.X (i, j)))))
```
-/
@[simp] theorem generalLinearCounitPointsMulEquiv_apply (i j : Fin n) :
    generalLinearCounitPointsMulEquiv n g i j =
      TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) B
        (g.ofConv (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
          (TauCeti.GeneralLinear.coordinateRingMap K n (MvPolynomial.X (i, j))))) := by
  rw [GeneralLinearCounitPointsMulEquiv.eq_pointsMulEquiv,
    TauCeti.GeneralLinear.pointsMulEquiv_apply,
    TauCeti.GeneralLinear.pointToGeneralLinear_apply,
    TauCeti.AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
  rfl

/-- The equality is

```lean
((generalLinearCounitPointsMulEquiv n g)⁻¹ : Matrix.GeneralLinearGroup (Fin n) B) i j =
      TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) B
        ((g⁻¹).ofConv (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
          (TauCeti.GeneralLinear.coordinateRingMap K n (MvPolynomial.X (i, j)))))
```
-/
@[simp] theorem GeneralLinearCounitPointsMulEquiv.inv_apply (i j : Fin n) :
    ((generalLinearCounitPointsMulEquiv n g)⁻¹ : Matrix.GeneralLinearGroup (Fin n) B) i j =
      TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) B
        ((g⁻¹).ofConv (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
          (TauCeti.GeneralLinear.coordinateRingMap K n (MvPolynomial.X (i, j))))) := by
  rw [← map_inv (generalLinearCounitPointsMulEquiv n) g,
    generalLinearCounitPointsMulEquiv_apply]

private theorem generalLinear_convMul_apply_X
    (f h : WithConv (TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₗ[K]
      TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) B))
    (i j : Fin n) :
    (f * h).ofConv (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
      (TauCeti.GeneralLinear.coordinateRingMap K n (MvPolynomial.X (i, j)))) =
      ∑ k : Fin n,
        f.ofConv (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
          (TauCeti.GeneralLinear.coordinateRingMap K n (MvPolynomial.X (i, k)))) *
        h.ofConv (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
          (TauCeti.GeneralLinear.coordinateRingMap K n (MvPolynomial.X (k, j)))) := by
  simp

/-- On counit-valued points, the tangent adjoint is matrix conjugation. -/
theorem generalLinear_tangentMatrix_adDerivation :
    TauCeti.GeneralLinear.tangentMatrix n (Derivation.adDerivation B g d) =
      (generalLinearCounitPointsMulEquiv n g : Matrix (Fin n) (Fin n) B) *
        TauCeti.GeneralLinear.tangentMatrix n d *
          ((generalLinearCounitPointsMulEquiv n g)⁻¹ :
            Matrix.GeneralLinearGroup (Fin n) B) := by
  ext i j
  rw [TauCeti.GeneralLinear.tangentMatrix_apply, Derivation.adDerivation_apply,
    generalLinear_convMul_apply_X, map_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, generalLinear_convMul_apply_X, map_sum, Matrix.mul_apply,
    GeneralLinearCounitPointsMulEquiv.inv_apply]
  congr 1

end ReductiveGroups
