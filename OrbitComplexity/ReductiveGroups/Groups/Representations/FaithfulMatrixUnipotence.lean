import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Faithful
import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Faithful Matrix Unipotence

A faithful coordinate representation detects unipotence of
original affine-group points from its evaluated matrix. -/

noncomputable section
namespace ReductiveGroups
open WithConv Module

universe u
variable {K B L : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  [Field L] [Algebra K L] [PerfectField L]

omit [PerfectField L] in
private theorem faithfulComodule_endOfPoint_matrix
    (M : TauCeti.FGComoduleCat K B) (n : ℕ) (b : Basis (Fin n) K M)
    (g : WithConv (B →ₐ[K] L)) :
    LinearMap.toMatrix (b.baseChange L) (b.baseChange L)
      (TauCeti.Comodule.endOfPoint M g.ofConv) =
      (TauCeti.Comodule.coefficientMatrix (C := B) b).map g.ofConv :=
  TauCeti.Comodule.toMatrix_endOfPoint b g.ofConv

/-- The matrix of a faithful finite comodule detects unipotence of
every original-group point over a perfect value field. Surjectivity of its
coordinate morphism proves faithfulness rather than assuming it. -/
theorem FaithfulMatrixUnipotence.isUnipotentPoint_matrix_nilpotent
    (M : TauCeti.FGComoduleCat.{u,u,u} K B) (n : ℕ) (b : Basis (Fin n) K M)
    (hρ : Function.Surjective (TauCeti.Comodule.coordinateBialgHom (H := B) b))
    (g : WithConv (B →ₐ[K] L))
    (h : IsNilpotent (((TauCeti.GeneralLinear.pointsMulEquiv n
      (TauCeti.AlgHom.mapDomain (TauCeti.Comodule.coordinateBialgHom (H := B) b) g) :
        Matrix (Fin n) (Fin n) L) - 1))) :
    TauCeti.HopfAlgebra.IsUnipotentPoint g := by
  have hM : TauCeti.Comodule.IsFaithful (k := K) (H := B) (V := M) :=
    (TauCeti.Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b).mpr
      ((TauCeti.Comodule.isClosedImmersion_coordinateGroupSchemeHom_iff b).mpr hρ)
  have hmat : LinearMap.toMatrix (b.baseChange L) (b.baseChange L)
      (TauCeti.Comodule.endOfPoint M g.ofConv) =
      (TauCeti.GeneralLinear.pointsMulEquiv n
        (TauCeti.AlgHom.mapDomain (TauCeti.Comodule.coordinateBialgHom (H := B) b) g) :
          Matrix (Fin n) (Fin n) L) := by
    rw [faithfulComodule_endOfPoint_matrix]
    symm
    exact AlgHom.pointsMulEquiv_comp_coordinateBialgHom g.ofConv b
  have hlinear : IsNilpotent (TauCeti.Comodule.endOfPoint M g.ofConv - 1) := by
    apply (IsNilpotent.map_iff
      (LinearMap.toMatrixAlgEquiv (b.baseChange L)).injective).mp
    have hsub := (LinearMap.toMatrixAlgEquiv (b.baseChange L)).map_sub
      (TauCeti.Comodule.endOfPoint M g.ofConv) 1
    change (LinearMap.toMatrixAlgEquiv (b.baseChange L))
        (TauCeti.Comodule.endOfPoint M g.ofConv - 1) =
        (LinearMap.toMatrixAlgEquiv (b.baseChange L))
          (TauCeti.Comodule.endOfPoint M g.ofConv) -
        (LinearMap.toMatrixAlgEquiv (b.baseChange L)) 1 at hsub
    have hcalc : (LinearMap.toMatrixAlgEquiv (b.baseChange L))
        (TauCeti.Comodule.endOfPoint M g.ofConv - 1) =
        (LinearMap.toMatrixAlgEquiv (b.baseChange L))
          (TauCeti.Comodule.endOfPoint M g.ofConv) - 1 := by
      simpa only [map_one] using hsub
    rw [hcalc]
    change IsNilpotent (LinearMap.toMatrix (b.baseChange L) (b.baseChange L)
      (TauCeti.Comodule.endOfPoint M g.ofConv) - 1)
    rw [hmat]
    exact h
  apply (TauCeti.HopfAlgebra.isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful
    M hM g).mpr
  apply (LinearMap.GeneralLinearGroup.isUnipotent_ofLinearEquiv_iff
    (TauCeti.Comodule.pointsAction M g)).mpr
  simpa only [TauCeti.Comodule.pointsAction_toLinearMap] using hlinear

end ReductiveGroups
