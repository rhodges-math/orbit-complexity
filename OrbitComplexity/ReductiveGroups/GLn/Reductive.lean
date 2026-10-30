import OrbitComplexity.ReductiveGroups.GLn.Points
import OrbitComplexity.ReductiveGroups.GLn.NormalUnipotent
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusMatrixInvariantSubspace
import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The general linear group is reductive

`GL_n` is smooth and geometrically connected. Over a field `L`, let `N` be a normal closed
subgroup which is smooth and whose points over an algebraic closure `L̄` are unipotent. Each
such point acts unipotently on the standard representation, whose matrix is the point itself;
so the matrix points of `N` form a normal subgroup of `GL_n(L̄)` consisting of unipotent
matrices, which is trivial. As `N` is reduced, the Nullstellensatz shows that its ideal is the
augmentation ideal, i.e. `N` is trivial. Reductivity over an arbitrary field follows because the
geometric fibre of `GL_n` over `K` is `GL_n` over `K̄`.

## Main declarations

* `ReductiveGroups.GLn.isNilpotent_quotientMatrixHom_sub_one`: a unipotent point of a closed
  subgroup of `GL_n` has a unipotent matrix.
* `ReductiveGroups.GLn.Reductive.of_isNormal_of_smoothUnipotent`: normal smooth unipotent closed
  subgroups of `GL_n` are trivial.
* `ReductiveGroups.GLn.reductive`: **`GL_n` is reductive** over every field.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §§11.21 and 14.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §19.5.
* J. S. Milne, *Algebraic Groups* (2017), Example 19.18 and §19.b.
* T. A. Springer, *Linear Algebraic Groups*, 2nd ed. (1998), §7.6.
-/

noncomputable section
namespace ReductiveGroups.GLn

open TauCeti TauCeti.GeneralLinear CategoryTheory WithConv
open scoped TensorProduct

universe u

section Standard

variable (L : Type u) [Field L] (n : ℕ)

/-- The coefficient matrix of the standard comodule of `GL_n` is the generic matrix. -/
theorem standardMatrixComodule_coefficientMatrix :
    letI := standardMatrixComodule L n
    Comodule.coefficientMatrix (C := coordinateHopfAlgebra L n) (Pi.basisFun L (Fin n)) =
      genericMatrix L n := by
  let _ := standardMatrixComodule L n
  ext i j
  rw [Comodule.coefficientMatrix_apply, Comodule.matrixCoefficient_def]
  change (TensorProduct.lid L (coordinateHopfAlgebra L n))
      (TensorProduct.map ((Pi.basisFun L (Fin n)).coord i) LinearMap.id
        (standardMatrixCoact L n (Pi.basisFun L (Fin n) j))) = _
  rw [standardMatrixCoact_basis]
  simp only [map_sum, TensorProduct.map_tmul, TensorProduct.lid_tmul,
    Module.Basis.coord_apply, Module.Basis.repr_self_apply, LinearMap.id_apply, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

variable {L n} (I : HopfIdeal L (coordinateHopfAlgebra L n))

/-- The standard representation restricted to the closed subgroup cut out by `I`. -/
@[instance_reducible]
def quotientStandardComodule :
    Comodule L (CommHopfAlgCat.quotient (coordinateHopfAlgebra L n) I) (Fin n → L) :=
  letI := standardMatrixComodule L n
  Comodule.Corestrict (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra L n) I).hom.toCoalgHom

/-- The coefficient matrix of the standard representation restricted to a closed subgroup
is the generic matrix reduced modulo that subgroup's defining ideal. -/
theorem QuotientStandardComodule.coefficientMatrix :
    letI := quotientStandardComodule I
    Comodule.coefficientMatrix (C := CommHopfAlgCat.quotient (coordinateHopfAlgebra L n) I)
        (Pi.basisFun L (Fin n)) =
      (genericMatrix L n).map (Ideal.Quotient.mk I.toIdeal) := by
  let _ := standardMatrixComodule L n
  have h := Comodule.coefficientMatrix_corestrict (C := coordinateHopfAlgebra L n)
    (Pi.basisFun L (Fin n))
    (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra L n) I).hom.toCoalgHom
  rw [standardMatrixComodule_coefficientMatrix] at h
  exact h

/-- **A unipotent point of a closed subgroup of `GL_n` has a unipotent matrix.** -/
theorem isNilpotent_quotientMatrixHom_sub_one {F : Type u} [Field F] [Algebra L F]
    (q : WithConv ((coordinateHopfAlgebra L n ⧸ I.toIdeal) →ₐ[L] F))
    (hq : HopfAlgebra.IsUnipotentPoint
      (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra L n) I) q) :
    IsNilpotent (((quotientMatrixHom I F q : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1) := by
  let _ := quotientStandardComodule I
  let M : FGComoduleCat.{u, u, u} L (CommHopfAlgCat.quotient (coordinateHopfAlgebra L n) I) :=
    FGComoduleCat.of (Fin n → L)
  have hlin := (HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one q).mp
    hq M
  let b := Pi.basisFun L (Fin n)
  have hmat : LinearMap.toMatrix (b.baseChange F) (b.baseChange F)
      (Comodule.endOfPoint M q.ofConv) =
      ((quotientMatrixHom I F q : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    have h1 := Comodule.toMatrix_endOfPoint (C := CommHopfAlgCat.quotient
      (coordinateHopfAlgebra L n) I) (M := Fin n → L) b q.ofConv
    refine h1.trans ?_
    rw [GLn.QuotientStandardComodule.coefficientMatrix, Matrix.map_map]
    ext i j
    simp only [quotientMatrixHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.map_apply,
      Function.comp_apply]
    rw [pointsMulEquiv_apply_apply, CommHopfAlgCat.quotientPointsHom_apply_apply]
    rfl
  have hnil : IsNilpotent (LinearMap.toMatrixAlgEquiv (b.baseChange F)
      (Comodule.endOfPoint M q.ofConv - 1)) := hlin.map _
  have hsub := (LinearMap.toMatrixAlgEquiv (b.baseChange F)).map_sub
    (Comodule.endOfPoint M q.ofConv) 1
  change (LinearMap.toMatrixAlgEquiv (b.baseChange F)) (Comodule.endOfPoint M q.ofConv - 1) =
    (LinearMap.toMatrixAlgEquiv (b.baseChange F)) (Comodule.endOfPoint M q.ofConv) -
      (LinearMap.toMatrixAlgEquiv (b.baseChange F)) 1 at hsub
  have hone : (LinearMap.toMatrixAlgEquiv (b.baseChange F)) 1 = 1 := map_one _
  rw [hsub, hone] at hnil
  change IsNilpotent (LinearMap.toMatrix (b.baseChange F) (b.baseChange F)
    (Comodule.endOfPoint M q.ofConv) - 1) at hnil
  rwa [hmat] at hnil

end Standard

section Normal

variable (L : Type u) [Field L] (n : ℕ)

/-- **A normal smooth closed subgroup of `GL_n` whose points over an algebraic closure are
unipotent is trivial.** -/
theorem Reductive.of_isNormal_of_smoothUnipotent
    (I : HopfIdeal L (finiteTypeCoordinateHopfAlgebra L n)) (hI : I.IsNormal)
    (hU : smoothUnipotentCommHopfAlgProperty L
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra L n) I)) :
    I = HopfIdeal.augmentation L (finiteTypeCoordinateHopfAlgebra L n) := by
  obtain ⟨hsmooth, hunip⟩ := (smoothUnipotentCommHopfAlgProperty_iff L _).mp hU
  let F := AlgebraicClosure L
  let I' : HopfIdeal L (coordinateHopfAlgebra L n) := I
  have hN : (matrixPoints I' F).Normal :=
    (CommHopfAlgCat.quotientPointsSubgroup_normal (coordinateHopfAlgebra L n) I' hI
      (CommAlgCat.of L F)).comap _
  have hnil : ∀ g ∈ matrixPoints I' F,
      IsNilpotent ((g : Matrix (Fin n) (Fin n) F) - 1) := by
    intro g hg
    obtain ⟨q, hq⟩ := quotientMatrixHom_surjective I' ⟨g, hg⟩
    have h := isNilpotent_quotientMatrixHom_sub_one I' q (hunip q)
    rw [hq] at h
    exact h
  have hbot := eq_bot_of_normal_of_forall_isNilpotent (matrixPoints I' F) hnil
  let _ : Algebra.Smooth L (coordinateHopfAlgebra L n ⧸ I'.toIdeal) := hsmooth
  have hred : IsReduced (coordinateHopfAlgebra L n ⧸ I'.toIdeal) :=
    TauCeti.isReduced_of_smooth L _
  have hrad : I'.toIdeal.IsRadical := (Ideal.isRadical_iff_quotient_reduced _).mpr hred
  have key : ∀ y : coordinateHopfAlgebra L n, Coalgebra.counit (R := L) y = 0 → y ∈ I' := by
    intro y hy
    rw [← HopfIdeal.mem_toIdeal]
    apply mem_of_forall_algHom_of_isRadical (k := L) (K := F) I'.toIdeal hrad
    intro f hf
    have hg : pointsMulEquiv n (toConv f) ∈ matrixPoints I' F :=
      (pointsMulEquiv_mem_matrixPoints_iff I' _).mpr
        (fun z hz => hf ((HopfIdeal.mem_toIdeal).mpr hz))
    rw [hbot, Subgroup.mem_bot] at hg
    have hone : toConv f = 1 := (pointsMulEquiv n).injective (hg.trans (map_one _).symm)
    have hf1 : f y = (1 : WithConv (coordinateHopfAlgebra L n →ₐ[L] F)).ofConv y := by
      rw [← hone]
    rw [hf1, AlgHom.convOne_apply, hy, map_zero]
  apply le_antisymm (HopfIdeal.le_augmentation L _ I)
  intro x hx
  rw [HopfIdeal.mem_augmentation] at hx
  exact key x hx

end Normal

/-- **The general linear group is reductive over every field.** -/
theorem reductive (K : Type u) [Field K] (n : ℕ) :
    reductiveCommHopfAlgProperty K (finiteTypeCoordinateHopfAlgebra K n) := by
  apply reductiveCommHopfAlgProperty_of_geometricFiber_iso K _
    (finiteTypeCoordinateHopfAlgebra (AlgebraicClosure K) n) (smooth K n)
    (geometricallyConnected K n)
    (finiteTypeCoordinateHopfAlgebraBaseChangeIso.{u, u} K (AlgebraicClosure K) n)
  intro I hI hU
  exact GLn.Reductive.of_isNormal_of_smoothUnipotent (AlgebraicClosure K) n I hI hU

end GLn
