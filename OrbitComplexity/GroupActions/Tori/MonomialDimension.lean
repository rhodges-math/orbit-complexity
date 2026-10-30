import OrbitComplexity.GroupActions.Tori.LatticeDimension
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-! # Dimensions of weight monoid algebras

Positive integral combinations of finitely many weights form a monoid. If the weights span
a lattice, inverting the product monomial gives its group algebra. Consequently the monoid
algebra has dimension equal to the lattice rank.

## Main definitions

* `GroupActions.weightMonoidHom`: the map sending nonnegative coefficients to their weight sum.

## Main results

* `GroupActions.ringKrullDim_weightMonoid`: the weight monoid algebra has the lattice rank as
  dimension.
-/

namespace GroupActions

open Multiplicative

universe u v

noncomputable section

variable {ι : Type u} [Fintype ι] {M : Type v} [AddCommGroup M]

/-- Nonnegative coefficients map to their weighted sum in the character lattice. -/
def weightMonoidHom (w : ι → M) : Multiplicative (ι → ℕ) →* Multiplicative M :=
  (Fintype.linearCombination ℕ w).toAddMonoidHom.toMultiplicative

private def weightSum (w : ι → M) : MonoidHom.mrange (weightMonoidHom w) :=
  ⟨weightMonoidHom w (ofAdd (fun _ ↦ 1)), ⟨ofAdd (fun _ ↦ 1), rfl⟩⟩

private theorem weight_cofinal (w : ι → M) (hw : Submodule.span ℤ (Set.range w) = ⊤)
    (y : Multiplicative M) :
    ∃ n : ℕ, y * (weightSum w).val ^ n ∈
      Set.range (MonoidHom.mrange (weightMonoidHom w)).subtype := by
  classical
  have hs : Function.Surjective (Fintype.linearCombination ℤ w) := by
    apply LinearMap.range_eq_top.mp
    rw [Fintype.range_linearCombination, hw]
  obtain ⟨z, hz⟩ := hs y.toAdd
  let n := Finset.univ.sup (fun i ↦ (-z i).toNat)
  have hn (i : ι) : 0 ≤ z i + (n : ℤ) := by
    have := Finset.le_sup (f := fun i ↦ (-z i).toNat) (Finset.mem_univ i)
    omega
  let q : ι → ℕ := fun i ↦ (z i + (n : ℤ)).toNat
  refine ⟨n, ⟨weightMonoidHom w (ofAdd q), ⟨ofAdd q, rfl⟩⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  change (∑ i, q i • w i) = y.toAdd + n • (∑ i, (1 : ℕ) • w i)
  rw [← hz, Fintype.linearCombination_apply]
  calc
    (∑ i, q i • w i) = ∑ i, (z i + (n : ℤ)) • w i := by
      apply Finset.sum_congr rfl
      intro i _
      change (z i + (n : ℤ)).toNat • w i = _
      rw [← Nat.cast_smul_eq_nsmul ℤ, Int.toNat_of_nonneg (hn i)]
    _ = _ := by
      simp only [add_zsmul, Finset.sum_add_distrib, natCast_zsmul, one_smul, Finset.smul_sum]

/-- A finitely generated weight monoid has the rank of its generated lattice as dimension. -/
theorem ringKrullDim_weightMonoid (K : Type v) [Field K] [Module.Free ℤ M] [Module.Finite ℤ M]
    (w : ι → M) (hw : Submodule.span ℤ (Set.range w) = ⊤) :
    ringKrullDim (MonoidAlgebra K (MonoidHom.mrange (weightMonoidHom w))) =
      (Module.finrank ℤ M : WithBot ℕ∞) := by
  let P := MonoidHom.mrange (weightMonoidHom w)
  let S := MonoidAlgebra K P
  let T := MonoidAlgebra K (Multiplicative M)
  let b := Module.Free.chooseBasis ℤ M
  have : UniqueSums M := UniqueSums.of_injective_addHom
    b.repr.toAddEquiv.toAddMonoidHom.toAddHom b.repr.injective inferInstance
  have : UniqueProds P := UniqueProds.of_injective_mulHom
    P.subtype.toMulHom Subtype.val_injective inferInstance
  have : IsDomain S := inferInstance
  have : Algebra.FiniteType K S := inferInstance
  let : Algebra S T := (MonoidAlgebra.mapDomainRingHom K P.subtype).toAlgebra
  have : IsLocalization.Away (MonoidAlgebra.single (weightSum w) (1 : K)) T :=
    TauCeti.MonoidAlgebra.isLocalization_away_mapDomainRingHom K P.subtype
      Subtype.val_injective (weightSum w) (Group.isUnit _) (weight_cofinal w hw)
  have hr : (MonoidAlgebra.single (weightSum w) (1 : K) : S) ≠ 0 :=
    MonoidAlgebra.single_ne_zero.mpr one_ne_zero
  let e := IsLocalization.algEquiv (Submonoid.powers
    (MonoidAlgebra.single (weightSum w) (1 : K) : S)) T
      (Localization.Away (MonoidAlgebra.single (weightSum w) (1 : K) : S))
  calc
    ringKrullDim S = ringKrullDim
        (Localization.Away (MonoidAlgebra.single (weightSum w) (1 : K) : S)) :=
      (TauCeti.ringKrullDim_localization_away K hr).symm
    _ = ringKrullDim T := (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm
    _ = _ := ringKrullDim_lattice K M

end

end GroupActions
