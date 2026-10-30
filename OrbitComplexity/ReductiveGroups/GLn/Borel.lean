import OrbitComplexity.ReductiveGroups.GLn.Points
import OrbitComplexity.ReductiveGroups.GLn.UpperTriangularQuotient
import OrbitComplexity.ReductiveGroups.GLn.SolvableOvergroup
import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed

/-!
# The upper-triangular subgroup is a Borel subgroup of `GL_n`

Over an algebraically closed field `L`, the upper-triangular subgroup `B` of `GL_n` is smooth
(its coordinate ring is an integral domain, hence reduced), connected (irreducible), and
solvable (its points form the solvable group of invertible upper-triangular matrices). It is
maximal among smooth, connected, solvable closed subgroups: if `Q` is such a subgroup containing
`B`, its matrix points form a solvable subgroup of `GL_n(L̄)` containing all invertible
upper-triangular matrices, hence consist of upper-triangular matrices; since `Q` is reduced, the
Nullstellensatz gives `Q = B`.

Over an arbitrary field `K` the Borel condition is imposed after base change to an algebraic
closure; the base change of the upper-triangular ideal is again the upper-triangular ideal.

## Main declarations

* `ReductiveGroups.GLn.upperTriangular_isBorelOverAlgClosed`: the Borel property over an
algebraically
  closed field.
* `ReductiveGroups.GLn.isBorel_upperTriangularIdeal`: the upper-triangular subgroup of `GL_n` is a
  Borel subgroup over every field.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.1 and Example 11.3.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §21.3.
* J. S. Milne, *Algebraic Groups* (2017), Example 17.3 and §17.a.
* T. A. Springer, *Linear Algebraic Groups*, 2nd ed. (1998), §6.2.
-/

noncomputable section
namespace ReductiveGroups.GLn

open TauCeti TauCeti.GeneralLinear CategoryTheory WithConv
open scoped TensorProduct

universe u

section AlgClosed

variable (L : Type u) [Field L] [IsAlgClosed L] (n : ℕ)

/-- The upper-triangular subgroup is smooth, connected and solvable. -/
theorem upperTriangular_isBorelCandidate :
    HopfIdeal.IsBorelCandidate L (finiteTypeCoordinateHopfAlgebra L n)
      (upperTriangularIdeal L n) := by
  let _ := isDomain_upperTriangularQuotient L n
  refine HopfIdeal.IsBorelCandidate.mk ?_ ?_ ?_
  · apply (smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed L _).mpr
    change IsReduced (coordinateHopfAlgebra L n ⧸ (upperTriangularIdeal L n).toIdeal)
    infer_instance
  · apply (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace L _).mpr
    change ConnectedSpace
      (PrimeSpectrum (coordinateHopfAlgebra L n ⧸ (upperTriangularIdeal L n).toIdeal))
    infer_instance
  · rw [geometricallySolvablePointsCommHopfAlgProperty_iff]
    have hsolv : Group.IsSolvable
        (matrixPoints (upperTriangularIdeal L n) (AlgebraicClosure L)) := by
      rw [matrixPoints_upperTriangularIdeal]
      exact isSolvable_upperTriangularGroup _ _
    exact isSolvable_quotientPoints (upperTriangularIdeal L n)

/-- Every smooth, connected, solvable closed subgroup containing the upper-triangular subgroup
equals it. -/
theorem upperTriangular_le_of_isBorelCandidate (Q : HopfIdeal L (coordinateHopfAlgebra L n))
    (hQ : HopfIdeal.IsBorelCandidate L (finiteTypeCoordinateHopfAlgebra L n) Q)
    (hle : Q ≤ upperTriangularIdeal L n) : upperTriangularIdeal L n ≤ Q := by
  let F := AlgebraicClosure L
  have hsolv : Group.IsSolvable
      (WithConv ((coordinateHopfAlgebra L n ⧸ Q.toIdeal) →ₐ[L] F)) :=
    hQ.geometricallySolvable
  have hsolvM : Group.IsSolvable (matrixPoints Q F) := isSolvable_matrixPoints Q
  have hUT : upperTriangularGroup F n ≤ matrixPoints Q F := by
    rw [← matrixPoints_upperTriangularIdeal L F]
    exact matrixPoints_antitone hle
  obtain ⟨c, hc0, hc⟩ := exists_sq_ne_one (F := F)
  have hS := le_upperTriangularGroup_of_isSolvable (matrixPoints Q F) hUT hc0 hc
  have hred : IsReduced (coordinateHopfAlgebra L n ⧸ Q.toIdeal) :=
    (smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed L _).mp hQ.smooth
  have hrad : Q.toIdeal.IsRadical := (Ideal.isRadical_iff_quotient_reduced _).mpr hred
  intro x hx
  rw [← HopfIdeal.mem_toIdeal]
  apply mem_of_forall_algHom_of_isRadical (k := L) (K := F) Q.toIdeal hrad
  intro f hf
  have hfQ : pointsMulEquiv n (toConv f) ∈ matrixPoints Q F :=
    (pointsMulEquiv_mem_matrixPoints_iff Q _).mpr
      (fun y hy => hf ((HopfIdeal.mem_toIdeal).mpr hy))
  have hfU := hS hfQ
  rw [← matrixPoints_upperTriangularIdeal L F, pointsMulEquiv_mem_matrixPoints_iff] at hfU
  exact hfU x hx

/-- **The upper-triangular subgroup of `GL_n` is a Borel subgroup over an algebraically closed
field.** -/
theorem upperTriangular_isBorelOverAlgClosed :
    HopfIdeal.IsBorelOverAlgClosed L (finiteTypeCoordinateHopfAlgebra L n)
      (upperTriangularIdeal L n) :=
  ⟨inferInstance, upperTriangular_isBorelCandidate L n,
    fun Q hQ hle => upperTriangular_le_of_isBorelCandidate L n Q hQ hle⟩

end AlgClosed

section BaseChange

variable (K L : Type u) [Field K] [Field L] [Algebra K L] (n : ℕ)

/-- The equality is

```lean
(coordinateHopfAlgebraBaseChangeIso.{u, u} K L n).hom.hom
        ((1 : L) ⊗ₜ[K] genericMatrix K n i j) = genericMatrix L n i j
```
-/
theorem baseChangeIso_one_tmul_genericMatrix (i j : Fin n) :
    (coordinateHopfAlgebraBaseChangeIso.{u, u} K L n).hom.hom
        ((1 : L) ⊗ₜ[K] genericMatrix K n i j) = genericMatrix L n i j := by
  rw [genericMatrix_apply, genericMatrix_apply,
    coordinateHopfAlgebraBaseChangeIso_hom_apply, MvPolynomial.map_X, one_smul]

/-- Base change carries the upper-triangular ideal to the upper-triangular ideal. -/
theorem Borel.map_upperTriangularIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := L) (upperTriangularIdeal K n)).map
        (coordinateHopfAlgebraBaseChangeIso.{u, u} K L n).hom.hom =
      upperTriangularIdeal L n := by
  apply CommHopfAlgCat.map_baseChangeHopfIdeal_of_toIdeal_eq_span _ _
    (coordinateHopfAlgebraBaseChangeIso.{u, u} K L n)
    (upperTriangularIdeal_toIdeal K n) (upperTriangularIdeal_toIdeal L n)
  ext y
  constructor
  · rintro ⟨x, ⟨i, j, hij, rfl⟩, rfl⟩
    exact ⟨i, j, hij, (baseChangeIso_one_tmul_genericMatrix K L n i j).symm⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨genericMatrix K n i j, ⟨i, j, hij, rfl⟩,
      baseChangeIso_one_tmul_genericMatrix K L n i j⟩

end BaseChange

/-- **The upper-triangular subgroup of `GL_n` is a Borel subgroup over every field.** -/
theorem isBorel_upperTriangularIdeal (K : Type u) [Field K] (n : ℕ) :
    HopfIdeal.IsBorel K (coordinateHopfAlgebra K n) (upperTriangularIdeal K n) := by
  refine (HopfIdeal.isBorel_iff_isBorelOverAlgClosed_baseChange K _ _).mpr ?_
  exact HopfIdeal.IsBorelOverAlgClosed.of_map_eq
    (finiteTypeCoordinateHopfAlgebraBaseChangeIso.{u, u} K (AlgebraicClosure K) n)
    (GLn.Borel.map_upperTriangularIdeal K (AlgebraicClosure K) n)
    (upperTriangular_isBorelOverAlgClosed (AlgebraicClosure K) n)

end GLn
