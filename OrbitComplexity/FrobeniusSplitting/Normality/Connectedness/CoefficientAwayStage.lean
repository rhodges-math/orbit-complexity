import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Batteries.Tactic.Lint

/-! # Principal localizations of coefficient subalgebras

A nonzero coefficient can be inverted inside the ambient field while
retaining a finitely generated coefficient subalgebra.
-/

set_option autoImplicit false

noncomputable section
universe u

namespace FrobeniusSplitting

private theorem exists_away_subalgebra {R K : Type u}
    [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) (r : R) (hr : r ≠ 0) :
    ∃ A : Subalgebra R K, IsLocalization.Away r A := by
  have hM : Submonoid.powers r ≤ nonZeroDivisors R :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hr)
  have hu : ∀ s : Submonoid.powers r, IsUnit (algebraMap R K s) := by
    rintro ⟨s, hs⟩
    apply isUnit_iff_ne_zero.mpr
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp (hM hs))
      (hinj (h.trans (map_zero (algebraMap R K)).symm))
  let f : Localization.Away r →ₐ[R] K :=
    { toRingHom := IsLocalization.lift hu
      commutes' := fun a => IsLocalization.lift_eq hu a }
  have hlocal : Function.Injective (algebraMap R (Localization.Away r)) :=
    IsLocalization.injective (Localization.Away r) hM
  have hf : Function.Injective f :=
    (IsLocalization.lift_injective_iff hu).mpr fun a b =>
      ⟨fun h => congrArg (algebraMap R K) (hlocal h),
        fun h => congrArg (algebraMap R (Localization.Away r)) (hinj h)⟩
  let E : Localization.Away r ≃ₐ[R] f.range :=
    AlgEquiv.ofBijective f.rangeRestrict
      ⟨fun a b h => hf (Subtype.ext_iff.mp h), Set.rangeFactorization_surjective⟩
  exact ⟨f.range, IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r) E⟩

/-- Inverting a nonzero element of a finitely generated coefficient
subalgebra gives a larger finitely generated subalgebra of the same field.
Its algebra structure is the prescribed coefficient inclusion. -/
theorem exists_coefficient_away {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) (r : S) (hr : r ≠ 0) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T), T.FG ∧
      letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      IsLocalization.Away r T := by
  obtain ⟨A, hA⟩ := exists_away_subalgebra
    (R := S) (K := K) Subtype.val_injective r hr
  let T : Subalgebra ℤ K := A.restrictScalars ℤ
  have hST : S ≤ T := by
    intro s hs
    exact A.algebraMap_mem (⟨s, hs⟩ : S)
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let E : A ≃ₐ[S] T :=
    { RingEquiv.refl A with commutes' := fun _ => rfl }
  let : IsLocalization.Away r A := hA
  let : IsLocalization.Away r T :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r) E
  let : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
  let : Algebra.FiniteType S T :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers r) T
  have hT : Algebra.FiniteType ℤ T :=
    Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType ℤ S) (inferInstance : Algebra.FiniteType S T)
  exact ⟨T, hST, (Subalgebra.fg_iff_finiteType T).mpr hT, inferInstance⟩

end FrobeniusSplitting
