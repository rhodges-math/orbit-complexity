import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaTangentDeterminesMorphism
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaUnitPointSubgroupCriterion
import OrbitComplexity.ReductiveGroups.Groups.Representations.ConjugateSubgroupTangent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# One point of an additive subgroup in a closed subgroup

In characteristic zero, if the parameter-one point of an additive one-parameter
subgroup lies in a closed subgroup, the whole one-parameter subgroup lies there.
Its natural-number parameters lie in the subgroup by the group law, and a
polynomial vanishing at all of them is zero.

## Main results

* `ReductiveGroups.gaTangent_mem_of_point_one_mem`: the tangent belongs to the subgroup tangent.
-/

noncomputable section

namespace ReductiveGroups

open TauCeti

universe u

variable {K B : Type u} [Field K] [CharZero K] [CommRing B] [HopfAlgebra K B]

/-- If the parameter-one point lies in a closed subgroup, its tangent lies in that subgroup. -/
theorem gaTangent_mem_of_point_one_mem
    (x : B →ₐc[K] SymmetricAlgebra K K) (I : HopfIdeal K B)
    (h : gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) ∈
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K)) :
    gaAffineGroupTangent x ∈
      (derivationCompLieHom (B := K)
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom).range := by
  apply (tangent_mem_hopfQuotient_iff I _).mpr
  intro b hb
  apply (Bialgebra.CounitAlgebra.algEquivSelf K B K).injective
  rw [map_zero, gaAffineGroupTangent, gaOriginDerivation_comp_apply,
    (GaMorphism.kills_hopfIdeal_iff_unitPoint_mem x I).mpr h b hb, map_zero, Polynomial.coeff_zero]

/-- A one-parameter subgroup with zero origin tangent has only identity points. -/
theorem gaPoints_eq_one_of_tangent_zero
    (x : B →ₐc[K] SymmetricAlgebra K K) (hx : gaAffineGroupTangent x = 0)
    (t : Multiplicative K) : gaAffineGroupPoints x t = 1 := by
  let z := (Bialgebra.unitBialgHom K (SymmetricAlgebra K K)).comp
    (Bialgebra.counitBialgHom K B)
  have hz : gaAffineGroupTangent z = 0 := by
    ext b
    apply (Bialgebra.CounitAlgebra.algEquivSelf K B K).injective
    rw [Derivation.zero_apply, map_zero, gaAffineGroupTangent, gaOriginDerivation_comp_apply]
    change ((gaPolynomialEquiv K)
      (algebraMap K (SymmetricAlgebra K K) (Coalgebra.counit b))).coeff 1 = 0
    simp
  have he := gaMorphism_ext_of_tangent_eq x z (hx.trans hz.symm)
  rw [he]
  apply WithConv.ofConv_injective
  ext b
  change ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm t).ofConv
    (algebraMap K (SymmetricAlgebra K K) (Coalgebra.counit b)) = _
  simp

/-- A parameter-one point in two closed subgroups with disjoint tangent images is the identity. -/
theorem gaPoint_one_eq_one_of_disjoint
    (x : B →ₐc[K] SymmetricAlgebra K K) (I J : HopfIdeal K B)
    (h : Disjoint (hopfTangentImage I).toSubmodule (hopfTangentImage J).toSubmodule)
    (hI : gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) ∈
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K))
    (hJ : gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) ∈
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) J (CommAlgCat.of K K)) :
    gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) = 1 := by
  have hmem : gaAffineGroupTangent x ∈
      (hopfTangentImage I).toSubmodule ⊓ (hopfTangentImage J).toSubmodule :=
    ⟨gaTangent_mem_of_point_one_mem x I hI, gaTangent_mem_of_point_one_mem x J hJ⟩
  rw [disjoint_iff.mp h] at hmem
  exact gaPoints_eq_one_of_tangent_zero x hmem _

end ReductiveGroups
