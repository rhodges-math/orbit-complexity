import OrbitComplexity.ReductiveGroups.Groups.TangentOperators.SquareZeroTangentPoint
import OrbitComplexity.ReductiveGroups.Lie.Roots.SquareZeroCommutator
import OrbitComplexity.ReductiveGroups.Groups.TangentOperators.PointConvolutionUnits
import OrbitComplexity.ReductiveGroups.Groups.TangentOperators.PointSquareZeroCommutator
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Naturality

/-!
# Square Zero Point Commutator

The point commutator on two independent square-zero parameters
has mixed coefficient equal to the original tangent Lie bracket. -/

noncomputable section
namespace ReductiveGroups

open TauCeti WithConv
open scoped commutatorElement

variable {K B A : Type*} [Field K] [CommRing B] [HopfAlgebra K B]
  [CommRing A] [Algebra K A]

private abbrev C := TauCeti.Bialgebra.CounitAlgebra K B K

private def tangentValueLinear (d : Derivation K B (C (K := K) (B := B))) :
    B →ₗ[K] A :=
  (Derivation.mapValue (A := B) (Algebra.ofId K A) d).toLinearMap

private def tangentValueConv (d : Derivation K B (C (K := K) (B := B))) :
    WithConv (B →ₗ[K] A) := toConv (tangentValueLinear (A := A) d)

private theorem squareZeroTangentPoint_linear
    (d : Derivation K B (C (K := K) (B := B)))
    (a : A) (ha : a * a = 0) :
    toConv (squareZeroTangentPoint d a ha).ofConv.toLinearMap =
      1 + a • tangentValueConv (A := A) d := by
  ext b
  change (squareZeroTangentPoint d a ha).ofConv b =
    ((1 + a • tangentValueConv (A := A) d) : WithConv (B →ₗ[K] A)).ofConv b
  rw [squareZeroTangentPoint_apply]
  simp [tangentValueConv, tangentValueLinear,
    TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_apply,
    LinearMap.convOne_apply]
  rfl

private theorem smulConv_square_zero
    (a : A) (ha : a * a = 0) (X : WithConv (B →ₗ[K] A)) :
    (a • X) * (a • X) = 0 := by
  rw [smul_mul_smul_comm, ha, zero_smul]

private theorem smulConv_mixed_cubic_zero
    (a b : A) (ha : a * a = 0)
    (X Y : WithConv (B →ₗ[K] A)) :
    (a • X) * (b • Y) * (a • X) = 0 := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm]
  have hab : a * b * a = 0 := by rw [mul_assoc, mul_comm b a, ← mul_assoc, ha, zero_mul]
  rw [hab, zero_smul]

private theorem tangentValueConv_lie
    (d e : Derivation K B (C (K := K) (B := B))) :
    tangentValueConv (A := A) ⁅d, e⁆ =
      tangentValueConv (A := A) d * tangentValueConv (A := A) e -
        tangentValueConv (A := A) e * tangentValueConv (A := A) d := by
  let φ : K →ₐ[K] A := Algebra.ofId K A
  have h := Derivation.mapValue_lie (A := B) φ d e
  have hbr := Derivation.coe_bracket
    (Derivation.mapValue (A := B) φ d) (Derivation.mapValue (A := B) φ e)
  ext b
  have hb := DFunLike.congr_fun hbr b
  have hbb := (DFunLike.congr_fun h b).trans hb.symm
  exact hbb

/-- The commutator of two square-zero tangent points is the
square-zero tangent point of their Lie bracket at the product
parameter.  -/
theorem squareZeroTangentPoint_commutator
    (d e : Derivation K B (C (K := K) (B := B)))
    (a b : A) (ha : a * a = 0) (hb : b * b = 0) :
    ⁅squareZeroTangentPoint d a ha, squareZeroTangentPoint e b hb⁆ =
      squareZeroTangentPoint ⁅d, e⁆ (a * b) (by
        calc
          (a * b) * (a * b) = (a * a) * (b * b) := by ring
          _ = 0 := by rw [ha, hb, zero_mul]) := by
  let X := tangentValueConv (A := A) d
  let Y := tangentValueConv (A := A) e
  let u := a • X
  let v := b • Y
  have hu : u * u = 0 := smulConv_square_zero a ha X
  have hv : v * v = 0 := smulConv_square_zero b hb Y
  have huvu : u * v * u = 0 := smulConv_mixed_cubic_zero a b ha X Y
  have hvuv : v * u * v = 0 := smulConv_mixed_cubic_zero b a hb Y X
  have hcomm := point_commutator_of_linear_squareZero
    (squareZeroTangentPoint d a ha) (squareZeroTangentPoint e b hb)
    u v (squareZeroTangentPoint_linear d a ha)
    (squareZeroTangentPoint_linear e b hb) hu hv huvu hvuv
  have hbr : u * v - v * u =
      (a * b) • tangentValueConv (A := A) ⁅d, e⁆ := by
    dsimp [u, v]
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm b a,
      ← smul_sub, tangentValueConv_lie]
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [hcomm, hbr]
  exact (squareZeroTangentPoint_linear ⁅d, e⁆ (a * b) _).symm

end ReductiveGroups
