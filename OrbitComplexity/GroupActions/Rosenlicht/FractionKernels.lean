import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.BaseChange
import OrbitComplexity.GroupActions.Rosenlicht.KernelTransport
import Mathlib.RingTheory.Flat.Localization

/-!
# Relation kernels in fraction-field realizations
-/

open scoped TensorProduct nonZeroDivisors

namespace GroupActions

noncomputable section

universe u v w z

/-- A tensor map from a generic scalar extension is injective whenever its
restriction to the original algebra is injective. -/
theorem fractionTensorMap_injective
    (R : Type u) [CommRing R] (F : Type v) [Field F] [Algebra R F]
    [IsFractionRing R F] (A : Type w) [CommRing A] [Algebra R A]
    (L : Type z) [CommRing L] [Algebra R L]
    (f : F →ₐ[R] L) (g : A →ₐ[R] L) (hg : Function.Injective g) :
    Function.Injective (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)) := by
  let : Algebra A (F ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let φ := Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (F ⊗[R] A) φ.toRingHom
  intro a ha
  have hga : g a = 0 := by
    change φ ((1 : F) ⊗ₜ[R] a) = 0 at ha
    simpa only [φ, Algebra.TensorProduct.lift_tmul, map_one, one_mul] using ha
  have hz : a = 0 := hg (hga.trans g.map_zero.symm)
  simp only [hz, map_zero]

end

end GroupActions

open MvPolynomial
open scoped TensorProduct nonZeroDivisors

namespace GroupActions

noncomputable section

universe u v w z a

/-- Polynomial relations in an injective fraction-field realization are the
scalar extension of the original polynomial relation ideal. -/
theorem ker_fraction_polynomial
    (R : Type u) [CommRing R] (F : Type v) [Field F] [Algebra R F]
    [IsFractionRing R F] (A : Type w) [CommRing A] [Algebra R A]
    (L : Type z) [CommRing L] [Algebra R L]
    (i : F →ₐ[R] L) (j : A →ₐ[R] L) (hj : Function.Injective j)
    {σ : Type a} (f : MvPolynomial σ R →ₐ[R] A) :
    RingHom.ker (MvPolynomial.eval₂Hom i.toRingHom (fun s ↦ j (f (X s)))) =
      (RingHom.ker f).map (MvPolynomial.map (algebraMap R F)) := by
  let φ := Algebra.TensorProduct.lift i j (fun _ _ ↦ Commute.all _ _)
  have hφ : Function.Injective φ := fractionTensorMap_injective R F A L i j hj
  have hC (c : F) : polynomialTensorMap F f (C c) = c ⊗ₜ[R] (1 : A) :=
    (polynomialTensorMap F f).commutes c
  have he : φ.toRingHom.comp (polynomialTensorMap F f).toRingHom =
      MvPolynomial.eval₂Hom i.toRingHom (fun s ↦ j (f (X s))) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      change φ (polynomialTensorMap F f (C c)) = i c
      rw [hC]
      simp only [φ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    · intro s
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      change φ (polynomialTensorMap F f (X s)) = j (f (X s))
      rw [polynomialTensorMap_X]
      simp only [φ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rw [← he, RingHom.ker_comp_of_injective (polynomialTensorMap F f).toRingHom hφ]
  let : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  exact ker_polynomialTensorMap_of_flat F f

end

end GroupActions
