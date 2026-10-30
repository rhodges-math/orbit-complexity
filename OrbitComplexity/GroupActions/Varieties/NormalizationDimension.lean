import OrbitComplexity.GroupActions.Varieties.NormalizationFibres

/-! # Dimension in a relative polynomial normalization

Over a field, nonempty open parts of integral affine schemes retain their dimensions.
An integral polynomial normalization after a base localization therefore computes the
dimension of the source as the dimension of the base plus its number of parameters.
-/

open MvPolynomial

namespace GroupActions

universe u

/-- A polynomial normalization over a nonempty base open computes the relative dimension. -/
theorem ringKrullDim_eq_add_of_normalization (K R A : Type u) [Field K] [CommRing R]
    [CommRing A] [IsDomain R] [IsDomain A] [Algebra K R] [Algebra K A] [Algebra R A]
    [Algebra.FiniteType K R] [Algebra.FiniteType K A] {n : ℕ}
    (x : Fin n → A) {r : R} (hr : r ≠ 0) (hinj : Function.Injective (algebraMap R A))
    (hx : Function.Injective (aeval x : MvPolynomial (Fin n) R →ₐ[R] A))
    (hint : (Localization.awayMap (aeval x).toRingHom (C r)).IsIntegral) :
    ringKrullDim A = ringKrullDim R + n := by
  let R' := Localization.Away r
  let A' := Localization.Away (algebraMap R A r)
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  have : IsNoetherianRing R' := inferInstance
  let : Algebra R' A' := (Localization.awayMap (algebraMap R A) r).toAlgebra
  have : IsScalarTower R R' A' :=
    .of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  obtain ⟨hj, hi⟩ := normalization_after_away (R' := R') (A' := A') x r hx hint
  let P := MvPolynomial (Fin n) R'
  let g : P →ₐ[R'] A' := aeval (fun i ↦ algebraMap A A' (x i))
  let : Algebra P A' := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral P A' := ⟨hi⟩
  have : FaithfulSMul P A' := (faithfulSMul_iff_algebraMap_injective P A').mpr hj
  have har : algebraMap R A r ≠ 0 := fun h ↦ hr (hinj (h.trans (map_zero _).symm))
  calc
    ringKrullDim A = ringKrullDim A' := (TauCeti.ringKrullDim_localization_away K har).symm
    _ = ringKrullDim P := TauCeti.ringKrullDim_eq_of_isIntegral_of_faithfulSMul
    _ = ringKrullDim R' + n := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, Nat.card_fin]
    _ = ringKrullDim R + n := by rw [TauCeti.ringKrullDim_localization_away K hr]

end GroupActions
