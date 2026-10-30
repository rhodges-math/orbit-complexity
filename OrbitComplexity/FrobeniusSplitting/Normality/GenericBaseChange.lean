import OrbitComplexity.FrobeniusSplitting.Normality.ArithmeticFibres
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Arithmetic fibers and field base change

A map that is surjective after localization remains surjective after any field extension in
which the denominators are invertible. Applied to finite algebras over a finite-type integer
algebra, closed-fiber surjectivity gives surjectivity of the base-changed algebra map.
An injective base-changed map to a normal domain is consequently an isomorphism of normal domains.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

private theorem localized_surj_clear {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (S : Submonoid R) (f : M →ₗ[R] N) (hf : Function.Surjective (LocalizedModule.map S f))
    (n : N) : ∃ s : S, ∃ m : M, f m = (s : R) • n := by
  obtain ⟨x, hx⟩ := hf (LocalizedModule.mk n 1)
  induction x using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hx
    obtain ⟨u, hu⟩ := hx
    simp only [Submonoid.smul_def, one_smul] at hu
    refine ⟨u * s, (u : R) • m, ?_⟩
    rw [f.map_smul]
    simpa only [Submonoid.coe_mul, mul_smul] using hu

/-- A localized surjective map is surjective after base change to an algebra
in which the denominators are units. -/
theorem baseChange_surjective_of_localized {R K M N : Type*} [CommRing R] [CommRing K]
    [Algebra R K] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (S : Submonoid R) (f : M →ₗ[R] N)
    (hS : ∀ s : S, IsUnit (algebraMap R K (s : R)))
    (hf : Function.Surjective (LocalizedModule.map S f)) :
    Function.Surjective (f.baseChange K) := by
  classical
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul k n =>
    obtain ⟨s, m, hm⟩ := localized_surj_clear S f hf n
    let u : Kˣ := (hS s).unit
    have hu : (u : K) = algebraMap R K (s : R) := (hS s).unit_spec
    refine ⟨((↑(u⁻¹) : K) * k) ⊗ₜ[R] m, ?_⟩
    rw [LinearMap.baseChange_tmul, hm, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    simp only [Algebra.smul_def, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb]⟩

/-- Generic surjectivity is preserved by extension to a field containing the base domain. -/
theorem baseChange_surjective_of_generic {R K M N : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [FaithfulSMul R K]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N)
    (hf : Function.Surjective (LocalizedModule.map (nonZeroDivisors R) f)) :
    Function.Surjective (f.baseChange K) := by
  apply baseChange_surjective_of_localized (nonZeroDivisors R) f ?_ hf
  intro s
  apply isUnit_iff_ne_zero.mpr
  intro hs
  apply (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
  apply FaithfulSMul.algebraMap_injective R K
  simpa only [map_zero] using hs

/-- Generic surjectivity of an algebra morphism is preserved by field base change. -/
theorem lTensor_surjective_of_generic {R K A B : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [FaithfulSMul R K] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (hf : Function.Surjective (LocalizedModule.map (nonZeroDivisors R) f.toLinearMap)) :
    Function.Surjective (Algebra.TensorProduct.lTensor (S := K) K f) := by
  have heq : (Algebra.TensorProduct.lTensor (S := K) K f).toLinearMap =
      f.toLinearMap.baseChange K := by
    rfl
  change Function.Surjective (Algebra.TensorProduct.lTensor (S := K) K f).toLinearMap
  rw [heq]
  exact baseChange_surjective_of_generic f.toLinearMap hf

universe u v

/-- Surjectivity on closed arithmetic fibers persists after extension to a field
containing the base domain. -/
theorem baseChange_surjective_closed_fibers {R A B : Type u} {K : Type v}
    [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] [Field K]
    [Algebra R K] [FaithfulSMul R K] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.Finite A B]
    (hf : ∀ p : PrimeSpectrum R, p.asIdeal.IsMaximal → (ringChar (R ⧸ p.asIdeal)).Prime →
      ∀ b : B, ∃ a : A,
      Ideal.Quotient.mk (p.asIdeal.map (algebraMap R B)) b =
        Ideal.Quotient.mk (p.asIdeal.map (algebraMap R B)) (algebraMap A B a)) :
    Function.Surjective (Algebra.TensorProduct.lTensor (S := K) K
      (IsScalarTower.toAlgHom R A B)) :=
  lTensor_surjective_of_generic (IsScalarTower.toAlgHom R A B)
    (surjective_generic_closed_fibers hf)

/-- A finite algebra map that is surjective on closed arithmetic fibers identifies its
field base change with a normal domain whenever the base-changed map is injective and its
target is a normal domain. -/
theorem normal_baseChange_of_closed_fibers {R A B : Type u} {K : Type v}
    [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] [Field K]
    [Algebra R K] [FaithfulSMul R K] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.Finite A B]
    [IsDomain (K ⊗[R] B)] [IsIntegrallyClosed (K ⊗[R] B)]
    (hi : Function.Injective (Algebra.TensorProduct.lTensor (S := K) K
      (IsScalarTower.toAlgHom R A B)))
    (hf : ∀ p : PrimeSpectrum R, p.asIdeal.IsMaximal → (ringChar (R ⧸ p.asIdeal)).Prime →
      ∀ b : B, ∃ a : A,
      Ideal.Quotient.mk (p.asIdeal.map (algebraMap R B)) b =
        Ideal.Quotient.mk (p.asIdeal.map (algebraMap R B)) (algebraMap A B a)) :
    IsDomain (K ⊗[R] A) ∧ IsIntegrallyClosed (K ⊗[R] A) := by
  let e := AlgEquiv.ofBijective (Algebra.TensorProduct.lTensor (S := K) K
    (IsScalarTower.toAlgHom R A B)) ⟨hi, baseChange_surjective_closed_fibers hf⟩
  exact ⟨e.toRingEquiv.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm.toRingEquiv⟩

end FrobeniusSplitting
