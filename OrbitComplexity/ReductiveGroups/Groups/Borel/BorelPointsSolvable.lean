import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
import Mathlib.GroupTheory.Solvable

/-!
# Borel Points Solvable

Geometric solvability of a fixed Borel quotient descends to its
ground-field-valued point group. -/

noncomputable section
namespace ReductiveGroups

open TauCeti CategoryTheory WithConv

universe u
variable {K : Type u} [Field K]

private theorem points_solvable_of_baseChangeIso
    (Q : CommHopfAlgCat K)
    (L : CommHopfAlgCat (AlgebraicClosure K))
    (e : L ≅ CommHopfAlgCat.baseChange (K := AlgebraicClosure K) Q)
    (hs : Group.IsSolvable
      (WithConv (L →ₐ[AlgebraicClosure K] AlgebraicClosure (AlgebraicClosure K)))) :
    Group.IsSolvable (WithConv (Q →ₐ[K] K)) := by
  let C := AlgebraicClosure K
  let D := AlgebraicClosure C
  let : Algebra K D := Algebra.compHom D (algebraMap K C)
  let : SMul K D := Algebra.toSMul
  let : IsScalarTower K C D := IsScalarTower.of_algebraMap_eq' rfl
  let E : WithConv (Q →ₐ[K] D) ≃* WithConv (L →ₐ[C] D) :=
    (AlgHom.baseChangePointsMulEquiv (k := K) (K := C) (A := Q) (R := D)).trans
      (AlgHom.mapDomainMulEquiv (A := D) (_root_.CommHopfAlgCat.ofIso e))
  have hsD : Group.IsSolvable (WithConv (Q →ₐ[K] D)) := by
    let : Group.IsSolvable (WithConv (L →ₐ[C] D)) := hs
    exact Group.isSolvable_of_isSolvable_injective
      (f := E.toMonoidHom) E.injective
  let : Group.IsSolvable (WithConv (Q →ₐ[K] D)) := hsD
  let f : K →ₐ[K] D := Algebra.ofId K D
  have hf : Function.Injective f := (algebraMap K D).injective
  exact Group.isSolvable_of_isSolvable_injective
    (f := AlgHom.mapValue (H := Q) f) (AlgHom.mapValue_injective hf)

private theorem borelQuotient_points_isSolvable_aux
    (H : CommHopfAlgCat K) [Algebra.FiniteType K H]
    (J : HopfIdeal K H) (hJ : HopfIdeal.IsBorel K H J) :
    Group.IsSolvable (WithConv ((CommHopfAlgCat.quotient H J) →ₐ[K] K)) := by
  let C := AlgebraicClosure K
  let H' := CommHopfAlgCat.baseChange (K := C) H
  let J' : HopfIdeal C H' := CommHopfAlgCat.baseChangeHopfIdeal (K := C) J
  let Q' := CommHopfAlgCat.quotient H' J'
  have hs0 := ((HopfIdeal.isBorel_iff K H J).mp hJ).2.2.1
  change Group.IsSolvable
    (WithConv (Q' →ₐ[C] AlgebraicClosure C)) at hs0
  let e : Q' ≅ CommHopfAlgCat.baseChange (K := C)
      (CommHopfAlgCat.quotient H J) :=
    CommHopfAlgCat.quotientBaseChangeIso (K := C) J
  exact points_solvable_of_baseChangeIso (CommHopfAlgCat.quotient H J) Q' e hs0

variable {B : Type u} [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

set_option maxHeartbeats 400000

/-- The `K`-points of the original Borel quotient form a solvable group. -/
theorem borelQuotient_points_isSolvable (J : HopfIdeal K B)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J) :
    Group.IsSolvable (WithConv ((B ⧸ J.toIdeal) →ₐ[K] K)) := by
  exact borelQuotient_points_isSolvable_aux (CommHopfAlgCat.of K B) J hJ

end ReductiveGroups
