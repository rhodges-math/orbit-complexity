import TauCeti.RingTheory.KrullDimension.Fiber
import TauCeti.RingTheory.KrullDimension.FiniteType
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-! # Closed-point fibre dimension inequalities

Maximal ideals of an integral finite-type algebra over a field have height equal to
the dimension of the algebra. Noether normalization and going down reduce this to the
polynomial-ring height recursion. The height inequality for a fibre then bounds the
source dimension at every maximal ideal.

## Main results

* `GroupActions.height_eq_dim_of_finiteType`: maximal ideals have full height.
* `GroupActions.ringKrullDim_le_add_fiber`: dimension is bounded by base plus fibre.
-/

open MvPolynomial

namespace GroupActions

universe u v

variable {K : Type u} [Field K]

private theorem heightMvPolynomial {ι : Type v} [Finite ι] (P : Ideal (MvPolynomial ι K))
    [P.IsMaximal] :
    (P.height : WithBot ℕ∞) = Nat.card ι := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    let Q := P.comap (renameEquiv K e).toRingEquiv
    have : Q.IsMaximal := Ideal.comap_isMaximal_of_equiv _
    calc
      _ = (Q.height : WithBot ℕ∞) := by rw [RingEquiv.height_comap]
      _ = Nat.card _ := ih Q
      _ = _ := by rw [Nat.card_congr e]
  | h_empty =>
    have hd : ringKrullDim (MvPolynomial PEmpty.{v + 1} K) = 0 := by simp
    simp only [Nat.card_eq_fintype_card, Fintype.card_pempty, Nat.cast_zero]
    apply le_antisymm
    · simpa [hd] using (Ideal.height_le_ringKrullDim_of_isPrime (I := P))
    · exact WithBot.coe_le_coe.mpr bot_le
  | @h_option ι _ ih =>
    let e := optionEquivLeft K ι
    let Q := P.comap e.symm.toRingEquiv
    have : Q.IsMaximal := Ideal.comap_isMaximal_of_equiv _
    let p := Q.under (MvPolynomial ι K)
    have : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
    rw [← e.symm.toRingEquiv.height_comap P,
      Polynomial.height_eq_height_add_one p Q, WithBot.coe_add, WithBot.coe_one, ih p]
    simp

/-- A maximal ideal of an integral finite-type algebra over a field has full height. -/
theorem height_eq_dim_of_finiteType (A : Type*) [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (P : Ideal A) [P.IsMaximal] :
    (P.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨n, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let R := MvPolynomial (Fin n) K
  let : Algebra R A := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral R A := ⟨hint⟩
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hinj
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have : IsDomain R := inferInstance
  have : UniqueFactorizationMonoid R := inferInstance
  have : IsIntegrallyClosed R := inferInstance
  have : Algebra.HasGoingDown R A := inferInstance
  let p := P.under R
  have : p.IsMaximal := inferInstance
  have hp : (p.height : WithBot ℕ∞) = ringKrullDim A := by
    rw [heightMvPolynomial (K := K) (ι := Fin n) p,
      TauCeti.ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g hinj hint, Nat.card_fin]
  apply le_antisymm Ideal.height_le_ringKrullDim_of_isPrime
  rw [← hp]
  apply WithBot.coe_le_coe.mpr
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P]
  exact le_add_of_nonneg_right bot_le

/-- The fibre under a maximal source ideal bounds the source dimension from below. -/
theorem ringKrullDim_le_add_fiber (R : Type*) (A : Type*)
    [CommRing R] [CommRing A] [Algebra K R] [Algebra K A]
    [Algebra.FiniteType K R] [Algebra.FiniteType K A] [IsDomain A] [Algebra R A]
    (P : Ideal A) [P.IsMaximal] :
    ringKrullDim A ≤ ringKrullDim R + ringKrullDim ((P.under R).Fiber A) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  rw [← height_eq_dim_of_finiteType (K := K) A P]
  refine (Ideal.height_le_height_add_ringKrullDim_fiber (P.under R) P).trans ?_
  gcongr
  exact Ideal.height_le_ringKrullDim_of_isPrime

end GroupActions
