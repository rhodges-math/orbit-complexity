import OrbitComplexity.GroupActions.Varieties.PointDifferentials
import OrbitComplexity.GroupActions.Varieties.PointCoefficients
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Differential criteria at rational points

Over an algebraically closed field, maximal residue fields of finite-type algebras are the base
field. Coefficient transport therefore reduces the smoothness and etaleness criteria to
precomposition of derivations valued at rational points.

## Main results

* `GroupActions.smooth_of_surjective_rationalDerivs`: rational tangent maps detect smoothness.
* `GroupActions.etale_of_bijective_rationalDerivs`: rational tangent maps detect etaleness.
-/

namespace GroupActions

noncomputable section

universe u v w x y

section Coefficients

variable {R : Type u} {A : Type v} {B : Type w} {C : Type x} {D : Type y}
  [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

private theorem surjective_pointPrecomp_coeff (e : C ≃ₐ[R] D)
    (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    Function.Surjective (pointDerivationPrecomp f g) ↔
      Function.Surjective (pointDerivationPrecomp f (e.toAlgHom.comp g)) := by
  let eS := pointDerivCoeffEquiv e g
  let eT := pointDerivCoeffEquiv e (g.comp f)
  have hfun : eT ∘ pointDerivationPrecomp f g =
      pointDerivationPrecomp f (e.toAlgHom.comp g) ∘ eS :=
    funext (pointDerivCoeffEquiv_comp e f g)
  calc
    _ ↔ Function.Surjective (eT ∘ pointDerivationPrecomp f g) :=
      (EquivLike.comp_surjective _ eT).symm
    _ ↔ Function.Surjective (pointDerivationPrecomp f (e.toAlgHom.comp g) ∘ eS) := by rw [hfun]; rfl
    _ ↔ _ := EquivLike.surjective_comp eS _

private theorem bijective_pointPrecomp_coeff (e : C ≃ₐ[R] D)
    (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    Function.Bijective (pointDerivationPrecomp f g) ↔
      Function.Bijective (pointDerivationPrecomp f (e.toAlgHom.comp g)) := by
  let eS := pointDerivCoeffEquiv e g
  let eT := pointDerivCoeffEquiv e (g.comp f)
  have hfun : eT ∘ pointDerivationPrecomp f g =
      pointDerivationPrecomp f (e.toAlgHom.comp g) ∘ eS :=
    funext (pointDerivCoeffEquiv_comp e f g)
  calc
    _ ↔ Function.Bijective (eT ∘ pointDerivationPrecomp f g) :=
      (EquivLike.comp_bijective _ eT).symm
    _ ↔ Function.Bijective (pointDerivationPrecomp f (e.toAlgHom.comp g) ∘ eS) := by rw [hfun]; rfl
    _ ↔ _ := EquivLike.bijective_comp eS _

end Coefficients

section ResidueFields

variable (K : Type u) (T : Type v) [Field K] [IsAlgClosed K]
  [CommRing T] [Algebra K T] [Algebra.FiniteType K T]

private def maxResidueFieldEquiv (ideal : Ideal T) [ideal.IsMaximal] :
    K ≃ₐ[K] IsLocalRing.ResidueField (Localization.AtPrime ideal) := by
  letI : Field (T ⧸ ideal) := Ideal.Quotient.field ideal
  have : Module.Finite K (T ⧸ ideal) := finite_of_finite_type_of_isJacobsonRing K (T ⧸ ideal)
  let e := (IsLocalization.AtPrime.equivQuotMaximalIdeal ideal
    (Localization.AtPrime ideal)).restrictScalars K
  have : Module.Finite K (IsLocalRing.ResidueField (Localization.AtPrime ideal)) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  exact AlgEquiv.ofBijective (Algebra.ofId K _) IsAlgClosed.algebraMap_bijective_of_isIntegral

end ResidueFields

section Algebras

variable (K : Type u) (S : Type v) (T : Type w)
  [Field K] [IsAlgClosed K] [CommRing S] [CommRing T]
  [Algebra K S] [Algebra K T] [Algebra S T] [IsScalarTower K S T]
  [Algebra.Smooth K S] [Algebra.Smooth K T] [Algebra.FinitePresentation S T]

/-- Surjective tangent precomposition at all rational points detects smoothness. -/
theorem smooth_of_surjective_rationalDerivs
    (hmap : ∀ p : T →ₐ[K] K, Function.Surjective
      (pointDerivationPrecomp (IsScalarTower.toAlgHom K S T) p)) : Algebra.Smooth S T := by
  apply smooth_of_surjective_pointDerivations K S T
  intro ideal hmaximal
  let q := IsScalarTower.toAlgHom K T (IsLocalRing.ResidueField (Localization.AtPrime ideal))
  let e := maxResidueFieldEquiv K T ideal
  let p : T →ₐ[K] K := e.symm.toAlgHom.comp q
  have hp := (surjective_pointPrecomp_coeff e (IsScalarTower.toAlgHom K S T) p).mp (hmap p)
  have hpq : e.toAlgHom.comp p = q := by ext t; exact e.apply_symm_apply (q t)
  erw [hpq] at hp
  exact hp

/-- Bijective tangent precomposition at all rational points detects etaleness. -/
theorem etale_of_bijective_rationalDerivs
    (hmap : ∀ p : T →ₐ[K] K, Function.Bijective
      (pointDerivationPrecomp (IsScalarTower.toAlgHom K S T) p)) : Algebra.Etale S T := by
  apply etale_of_bijective_pointDerivations K S T
  intro ideal hmaximal
  let q := IsScalarTower.toAlgHom K T (IsLocalRing.ResidueField (Localization.AtPrime ideal))
  let e := maxResidueFieldEquiv K T ideal
  let p : T →ₐ[K] K := e.symm.toAlgHom.comp q
  have hp := (bijective_pointPrecomp_coeff e (IsScalarTower.toAlgHom K S T) p).mp (hmap p)
  have hpq : e.toAlgHom.comp p = q := by ext t; exact e.apply_symm_apply (q t)
  erw [hpq] at hp
  exact hp

end Algebras

end

end GroupActions
