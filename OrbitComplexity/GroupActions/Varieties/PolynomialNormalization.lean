import OrbitComplexity.GroupActions.Varieties.RelativeNormalization
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.MvPolynomial.Localization
import TauCeti.RingTheory.KrullDimension.FiniteType

/-! # Polynomial parameters after localization

Noether normalization over a localized field can be chosen with parameters coming from
the original algebra. Multiplying every parameter by one invertible base element preserves
both algebraic independence and integrality of the polynomial map.
-/

open MvPolynomial

namespace GroupActions

noncomputable section

universe u v w z t

private def scaleVariables {R : Type u} [CommRing R] (ι : Type v) (c : Rˣ) :
    MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R :=
  AlgEquiv.ofAlgHom (aeval fun i ↦ (c : R) • X i)
    (aeval fun i ↦ ((c⁻¹ : Rˣ) : R) • X i)
    (by ext i; simp [smul_smul]) (by ext i; simp [smul_smul])

variable {R : Type u} {A : Type v} {k : Type w} {B : Type z}
  [CommRing R] [CommRing A] [Field k] [CommRing B] [Algebra R A] [Algebra R k]
  [Algebra A B] [Algebra R B] [Algebra k B] [IsScalarTower R A B] [IsScalarTower R k B]

/-- Polynomial normalization parameters over a localized field can come from the original ring. -/
theorem exists_integral_parameters (M : Submonoid R) [IsLocalization M k]
    [IsLocalization (Algebra.algebraMapSubmonoid A M) B] [Nontrivial B]
    [Algebra.FiniteType k B] :
    ∃ n : ℕ, ∃ x : Fin n → A,
      Function.Injective (aeval (fun i ↦ algebraMap A B (x i)) :
        MvPolynomial (Fin n) k →ₐ[k] B) ∧
      (aeval (fun i ↦ algebraMap A B (x i)) : MvPolynomial (Fin n) k →ₐ[k] B).IsIntegral := by
  classical
  obtain ⟨n, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k B
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Algebra.algebraMapSubmonoid A M) (fun i : Fin n ↦ g (X i))
  obtain ⟨a, ha, hab⟩ := b.property
  obtain ⟨c, hc⟩ := IsLocalization.map_units k (⟨a, ha⟩ : M)
  choose x hx using hb
  let e := scaleVariables (Fin n) c
  have he : (g.comp e.toAlgHom) = aeval (fun i ↦ algebraMap A B (x i)) := by
    ext i
    simp only [e, scaleVariables, AlgEquiv.toAlgHom_ofAlgHom, AlgHom.comp_apply, aeval_X]
    rw [map_smul, hc]
    have h := hx i
    simpa only [Algebra.smul_def, ← hab, ← IsScalarTower.algebraMap_apply R A B,
      ← IsScalarTower.algebraMap_apply R k B] using h.symm
  refine ⟨n, x, ?_, ?_⟩
  · rw [← he]
    exact hg.comp e.injective
  · rw [← he]
    exact RingHom.IsIntegral.trans e.toRingHom g.toRingHom
      (RingHom.isIntegral_of_surjective e.toRingHom e.surjective) hint

private theorem aeval_localization_comp {ι : Type t} (x : ι → A) :
    (aeval (fun i ↦ algebraMap A B (x i)) : MvPolynomial ι k →ₐ[k] B).toRingHom.comp
        (MvPolynomial.map (algebraMap R k)) =
      (algebraMap A B).comp (aeval x).toRingHom := by
  ext <;> simp [← IsScalarTower.algebraMap_apply R A B,
    ← IsScalarTower.algebraMap_apply R k B]

/-- Parameters whose field polynomial map is injective are algebraically independent over
the original base when its map into the field is injective. -/
theorem injective_aeval_of_localized {ι : Type t} (x : ι → A)
    (hinj : Function.Injective (algebraMap R k))
    (hx : Function.Injective (aeval (fun i ↦ algebraMap A B (x i)) :
      MvPolynomial ι k →ₐ[k] B)) :
    Function.Injective (aeval x : MvPolynomial ι R →ₐ[R] A) := by
  intro p q hpq
  apply MvPolynomial.map_injective (algebraMap R k) hinj
  apply hx
  change ((aeval (fun i ↦ algebraMap A B (x i)) : MvPolynomial ι k →ₐ[k] B).toRingHom.comp
      (MvPolynomial.map (algebraMap R k))) p =
    ((aeval (fun i ↦ algebraMap A B (x i)) : MvPolynomial ι k →ₐ[k] B).toRingHom.comp
      (MvPolynomial.map (algebraMap R k))) q
  rw [aeval_localization_comp x]
  exact congrArg (algebraMap A B) hpq

attribute [local instance] MvPolynomial.algebraMvPolynomial in
set_option maxHeartbeats 400000 in
/-- A normalization of the generic localization spreads to an integral polynomial map
over an open part of the original base. -/
theorem exists_relative_normalization (M : Submonoid R) [IsLocalization M k]
    [IsLocalization (Algebra.algebraMapSubmonoid A M) B] [Nontrivial B]
    [Algebra.FiniteType k B] [Algebra.FiniteType R A]
    (hinj : Function.Injective (algebraMap R k)) :
    ∃ n : ℕ, ∃ x : Fin n → A, ∃ m : M,
      Function.Injective (aeval x : MvPolynomial (Fin n) R →ₐ[R] A) ∧
      (Localization.awayMap (aeval x).toRingHom (C (m : R))).IsIntegral ∧
      ringKrullDim B = n := by
  classical
  obtain ⟨n, x, hx, hint⟩ := exists_integral_parameters (A := A) (k := k) (B := B) M
  let P := MvPolynomial (Fin n) R
  let Q := MvPolynomial (Fin n) k
  let f : P →ₐ[R] A := aeval x
  let g : Q →ₐ[k] B := aeval (fun i ↦ algebraMap A B (x i))
  have hdim : ringKrullDim B = n := by
    simpa only [Nat.card_fin] using
      TauCeti.ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g hx hint
  have hf : Function.Injective f := injective_aeval_of_localized (B := B) x hinj hx
  have hcomm : g.toRingHom.comp (MvPolynomial.map (algebraMap R k)) =
      (algebraMap A B).comp f.toRingHom := aeval_localization_comp x
  let : Algebra P A := f.toRingHom.toAlgebra
  let : Algebra P B := ((algebraMap A B).comp f.toRingHom).toAlgebra
  let : Algebra Q B := g.toRingHom.toAlgebra
  have : IsScalarTower R P A := .of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsScalarTower P A B := .of_algebraMap_eq' rfl
  have : IsScalarTower P Q B := .of_algebraMap_eq' hcomm.symm
  have : Algebra.FiniteType P A := Algebra.FiniteType.of_restrictScalars_finiteType R P A
  have : Algebra.IsIntegral Q B := ⟨hint⟩
  have he : Algebra.algebraMapSubmonoid A (M.map (C : R →+* P)) =
      Algebra.algebraMapSubmonoid A M := by
    rw [C_eq_algebraMap]
    exact Algebra.algebraMapSubmonoid_map_map M
  have : IsLocalization (Algebra.algebraMapSubmonoid A (M.map (C : R →+* P))) B := by
    rw [he]
    infer_instance
  obtain ⟨p, hp⟩ := exists_integral_away (R := P) (A := A) (Rₘ := Q) (Aₘ := B)
    (M.map (C : R →+* P))
  rcases p with ⟨p, hpM⟩
  obtain ⟨m, hm, rfl⟩ := hpM
  exact ⟨n, x, ⟨m, hm⟩, hf, hp, hdim⟩

end

end GroupActions
