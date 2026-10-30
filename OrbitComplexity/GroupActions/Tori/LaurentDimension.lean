import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Basic
import TauCeti.Algebra.MonoidAlgebra.Localization
import TauCeti.RingTheory.KrullDimension.FiniteType
import Mathlib.RingTheory.KrullDimension.Polynomial

/-! # Dimension of split torus coordinate rings

The group algebra of a free character lattice is the localization of the polynomial
monoid algebra away from the product of the variables. Its Krull dimension is the lattice rank.

## Main results

* `GroupActions.ringKrullDim_splitTorus`: the coordinate ring of a split torus has its rank
  as Krull dimension.
-/

namespace GroupActions

open Multiplicative

universe u

noncomputable section

private def exponentMap (ι : Type u) :
    Multiplicative (ι →₀ ℕ) →* Multiplicative (ι →₀ ℤ) :=
  (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)).toMultiplicative

private def allExponents (ι : Type u) [Fintype ι] : Multiplicative (ι →₀ ℕ) :=
  ofAdd (Finsupp.equivFunOnFinite.symm (fun _ ↦ 1))

private theorem exponentMap_injective (ι : Type u) : Function.Injective (exponentMap ι) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  ext i
  have hi := congrArg (fun z ↦ z.toAdd i) h
  exact Nat.cast_injective hi

private theorem exponentMap_all (ι : Type u) [Fintype ι] (i : ι) :
    (exponentMap ι (allExponents ι)).toAdd i = 1 := by
  simp [exponentMap, allExponents]

private theorem exponentMap_cofinal (ι : Type u) [Fintype ι]
    (y : Multiplicative (ι →₀ ℤ)) :
    ∃ n : ℕ, y * exponentMap ι (allExponents ι) ^ n ∈ Set.range (exponentMap ι) := by
  classical
  let n := Finset.univ.sup (fun i ↦ (-y.toAdd i).toNat)
  have hn (i : ι) : (-y.toAdd i).toNat ≤ n :=
    Finset.le_sup (f := fun i ↦ (-y.toAdd i).toNat) (Finset.mem_univ i)
  have hnonneg (i : ι) : 0 ≤ y.toAdd i + (n : ℤ) := by
    have := hn i
    omega
  let z : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i ↦ (y.toAdd i + (n : ℤ)).toNat)
  refine ⟨n, ofAdd z, ?_⟩
  apply Multiplicative.toAdd.injective
  ext i
  change (z i : ℤ) = y.toAdd i + n • (exponentMap ι (allExponents ι)).toAdd i
  rw [exponentMap_all, nsmul_eq_mul, mul_one]
  simpa only [z, Finsupp.equivFunOnFinite_symm_apply_apply] using
    Int.toNat_of_nonneg (hnonneg i)

private theorem torus_ringDim (K : Type u) [Field K] (ι : Type u) [Fintype ι] :
    ringKrullDim (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) = (Fintype.card ι : WithBot ℕ∞) := by
  let S := MonoidAlgebra K (Multiplicative (ι →₀ ℕ))
  let T := MonoidAlgebra K (Multiplicative (ι →₀ ℤ))
  let e : MvPolynomial ι K ≃ₐ[K] S :=
    AddMonoidAlgebra.toMultiplicativeAlgEquiv K K (ι →₀ ℕ)
  have : IsDomain S := e.symm.injective.isDomain e.symm.toRingHom
  have : Algebra.FiniteType K S := Algebra.FiniteType.of_surjective e.toAlgHom e.surjective
  let : Algebra S T := (MonoidAlgebra.mapDomainRingHom K (exponentMap ι)).toAlgebra
  have : IsLocalization.Away (MonoidAlgebra.single (allExponents ι) (1 : K)) T :=
    TauCeti.MonoidAlgebra.isLocalization_away_mapDomainRingHom K (exponentMap ι)
      (exponentMap_injective ι) (allExponents ι) (Group.isUnit _) (exponentMap_cofinal ι)
  have hr : (MonoidAlgebra.single (allExponents ι) (1 : K) : S) ≠ 0 := by
    exact MonoidAlgebra.single_ne_zero.mpr one_ne_zero
  let q := IsLocalization.algEquiv (Submonoid.powers
    (MonoidAlgebra.single (allExponents ι) (1 : K) : S)) T
      (Localization.Away (MonoidAlgebra.single (allExponents ι) (1 : K) : S))
  calc
    ringKrullDim T = ringKrullDim
        (Localization.Away (MonoidAlgebra.single (allExponents ι) (1 : K) : S)) :=
      ringKrullDim_eq_of_ringEquiv q.toRingEquiv
    _ = ringKrullDim S := TauCeti.ringKrullDim_localization_away K hr
    _ = ringKrullDim (MvPolynomial ι K) := ringKrullDim_eq_of_ringEquiv e.symm.toRingEquiv
    _ = (Fintype.card ι : WithBot ℕ∞) := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
        ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card]

/-- A finite-rank split torus coordinate ring has Krull dimension equal to its rank. -/
theorem ringKrullDim_splitTorus (K : Type u) [Field K] (ι : Type u) [Finite ι] :
    ringKrullDim (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) = (Nat.card ι : WithBot ℕ∞) := by
  let := Fintype.ofFinite ι
  simpa only [Nat.card_eq_fintype_card] using torus_ringDim K ι

end

end GroupActions
