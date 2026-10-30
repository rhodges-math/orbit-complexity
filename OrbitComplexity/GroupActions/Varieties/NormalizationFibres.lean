import OrbitComplexity.GroupActions.Varieties.PolynomialNormalization
import OrbitComplexity.GroupActions.Varieties.IntegralFibres
import Mathlib.RingTheory.RingHom.Integral

/-! # Localized polynomial normalizations and their fibres

Localizing the coefficients and parameters of a polynomial normalization gives the
same integral map in any models of the localizations. This identifies the relative
normalization with a polynomial map over the localized base.
-/

open MvPolynomial
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra A A'] [Algebra R A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

private theorem aeval_baseChange_comp {n : ℕ} (x : Fin n → A) :
    (aeval (fun i ↦ algebraMap A A' (x i)) :
        MvPolynomial (Fin n) R' →ₐ[R'] A').toRingHom.comp
          (MvPolynomial.map (algebraMap R R')) =
      (algebraMap A A').comp (aeval x).toRingHom := by
  ext <;> simp [← IsScalarTower.algebraMap_apply R A A',
    ← IsScalarTower.algebraMap_apply R R' A']

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- Localizing a polynomial normalization preserves its injection and its integrality. -/
theorem normalization_after_away {n : ℕ} (x : Fin n → A) (r : R)
    [IsLocalization.Away r R'] [IsLocalization.Away (algebraMap R A r) A']
    (hinj : Function.Injective (aeval x : MvPolynomial (Fin n) R →ₐ[R] A))
    (hint : (Localization.awayMap (aeval x).toRingHom (C r)).IsIntegral) :
    Function.Injective (aeval (fun i ↦ algebraMap A A' (x i)) :
      MvPolynomial (Fin n) R' →ₐ[R'] A') ∧
      (aeval (fun i ↦ algebraMap A A' (x i)) :
        MvPolynomial (Fin n) R' →ₐ[R'] A').IsIntegral := by
  let P := MvPolynomial (Fin n) R
  let Q := MvPolynomial (Fin n) R'
  let f : P →ₐ[R] A := aeval x
  let g : Q →ₐ[R'] A' := aeval (fun i ↦ algebraMap A A' (x i))
  have hfC : f (C r) = algebraMap R A r := MvPolynomial.aeval_C x r
  have : IsLocalization.Away (C r : P) Q := by
    simpa only [Submonoid.map_powers] using
      (inferInstance : IsLocalization ((Submonoid.powers r).map (C : R →+* P)) Q)
  have : IsLocalization.Away (f (C r)) A' := by
    rw [hfC]
    infer_instance
  have he : IsLocalization.Away.map Q A' f.toRingHom (C r) = g.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (C r : P))
    change (IsLocalization.map A' f.toRingHom _).comp (algebraMap P Q) = _
    rw [IsLocalization.map_comp]
    exact (aeval_baseChange_comp x).symm
  have hi : (IsLocalization.Away.map Q A' f.toRingHom (C r)).IsIntegral :=
    (RingHom.isIntegral_respectsIso.isLocalization_away_iff Q A' f.toRingHom (C r)).mp hint
  have hj : Function.Injective (IsLocalization.Away.map Q A' f.toRingHom (C r)) := by
    apply (IsLocalization.Away.map_injective_iff A' f.toRingHom (C r)).mpr
    intro p hp
    have hp' : p = 0 := hinj (hp.trans (map_zero f).symm)
    exact ⟨0, by simp [hp']⟩
  rw [he] at hi hj
  exact ⟨hj, hi⟩

end

noncomputable section

variable {R A k B : Type u} [CommRing R] [CommRing A] [Field k] [CommRing B]
  [Algebra R A] [Algebra R k] [Algebra A B] [Algebra R B] [Algebra k B]
  [IsScalarTower R A B] [IsScalarTower R k B]

/-- After one base localization, all field fibres have the generic algebra's dimension. -/
theorem exists_constant_fibre_dim (M : Submonoid R) [IsLocalization M k]
    [IsLocalization (Algebra.algebraMapSubmonoid A M) B] [Nontrivial B]
    [Algebra.FiniteType k B] [Algebra.FiniteType R A]
    (hinj : Function.Injective (algebraMap R k)) :
    ∃ m : M,
      let R' := Localization.Away (m : R)
      let A' := Localization.Away (algebraMap R A (m : R))
      letI : Algebra R' A' := (Localization.awayMap (algebraMap R A) (m : R)).toAlgebra
      ∀ (L : Type u) [Field L] [Algebra R' L],
        ringKrullDim (L ⊗[R'] A') = ringKrullDim B := by
  obtain ⟨n, x, m, hj, hi, hdim⟩ :=
    exists_relative_normalization (A := A) (k := k) (B := B) M hinj
  refine ⟨m, ?_⟩
  let R' := Localization.Away (m : R)
  let A' := Localization.Away (algebraMap R A (m : R))
  let : Algebra R' A' := (Localization.awayMap (algebraMap R A) (m : R)).toAlgebra
  have : IsScalarTower R R' A' :=
    .of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  obtain ⟨hj', hi'⟩ := normalization_after_away (R' := R') (A' := A') x (m : R) hj hi
  change ∀ (L : Type u) [Field L] [Algebra R' L],
    ringKrullDim (L ⊗[R'] A') = ringKrullDim B
  intro L _ _
  rw [hdim]
  exact ringKrullDim_fibre_of_normalization R' A' L n
    (aeval (fun i ↦ algebraMap A A' (x i))) hj' hi'

end

end GroupActions
