import OrbitComplexity.FrobeniusSplitting.Normality.LocalAlgebra
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Normality of étale algebras

The generic base change of an essentially finite type unramified algebra over a
domain is Artinian. For an étale algebra this is a total quotient ring, and smooth
base change commutes with integral closure. The same comparison after localization
proves that local rings of an étale algebra over a normal domain are normal domains.
-/

namespace FrobeniusSplitting

open scoped TensorProduct nonZeroDivisors
open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

private theorem regular_image [Module.Flat R S] :
    Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ := by
  rintro _ ⟨r, hr, rfl⟩
  rw [mem_nonZeroDivisors_iff_left]
  intro s hs
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors (M := S) hr
    (show r • s = r • (0 : S) by simpa [Algebra.smul_def] using hs)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem artinian_genericFiber [IsDomain R]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] :
    IsArtinianRing (S ⊗[R] FractionRing R) := by
  let K := FractionRing R
  let T := S ⊗[R] K
  have : Algebra.FormallyUnramified K T :=
    Algebra.FormallyUnramified.of_equiv (Algebra.TensorProduct.commRight R K S)
  have : Algebra.EssFiniteType K T :=
    Algebra.EssFiniteType.of_surjective
      (Algebra.TensorProduct.commRight R K S).toAlgHom
      (Algebra.TensorProduct.commRight R K S).surjective
  have : Module.Finite K T := Algebra.FormallyUnramified.finite_of_free K T
  exact isArtinian_of_tower K inferInstance

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Localizations of étale algebras over normal domains are integrally closed. -/
theorem isIntegrallyClosed_of_etale_loc {B : Type*} [CommRing B]
    [Algebra S B] [Algebra R B] [IsScalarTower R S B]
    [IsDomain R] [IsIntegrallyClosed R] [Algebra.Etale R S]
    (M : Submonoid S) [IsLocalization M B] : IsIntegrallyClosed B := by
  let K := FractionRing R
  let T := B ⊗[R] K
  let N := Algebra.algebraMapSubmonoid B R⁰
  have : Module.Flat S B := IsLocalization.flat B M
  have : Module.Flat R B := Module.Flat.trans R S B
  have : Algebra.FormallyUnramified S B :=
    Algebra.FormallyUnramified.of_isLocalization M
  have : Algebra.FormallyUnramified R B := Algebra.FormallyUnramified.comp R S B
  have : Algebra.EssFiniteType S B := Algebra.EssFiniteType.of_isLocalization B M
  have : Algebra.EssFiniteType R B := Algebra.EssFiniteType.comp R S B
  have hN : N ≤ B⁰ := regular_image
  have : IsArtinianRing T := artinian_genericFiber
  have : IsFractionRing B T := IsLocalization.of_le N B⁰ hN fun a ha ↦
    IsArtinianRing.isUnit_of_mem_nonZeroDivisors
      (IsLocalization.nonZeroDivisors_le_comap N T ha)
  apply (isIntegrallyClosed_iff T).mpr
  intro x hx
  have hcomp := TensorProduct.toIntegralClosure_bijective_of_tower
    (R := R) (S := S) (T := B) (B := K)
    TensorProduct.toIntegralClosure_bijective_of_smooth
    (TensorProduct.toIntegralClosure_bijective_of_isLocalization M)
  obtain ⟨y, hy⟩ := hcomp.2 ⟨x, hx⟩
  have himage (y : B ⊗[R] integralClosure R K) :
      ((TensorProduct.toIntegralClosure R B K) y : T) ∈ (⊥ : Subalgebra B T) := by
    induction y with
    | add y z hy hz => simpa only [map_add, Subalgebra.coe_add] using add_mem hy hz
    | tmul s k =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral k.2
      change s ⊗ₜ[R] (k : K) ∈ (⊥ : Subalgebra B T)
      rw [← hr]
      apply Algebra.mem_bot.mpr
      refine ⟨r • s, ?_⟩
      change (r • s) ⊗ₜ[R] (1 : K) = s ⊗ₜ[R] algebraMap R K r
      rw [smul_tmul, Algebra.smul_def, mul_one]
  have hyimage := himage y
  rw [hy] at hyimage
  exact Algebra.mem_bot.mp hyimage

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- A local localization of an étale algebra over a normal domain is a domain. -/
theorem isDomain_of_etale_local {B : Type*} [CommRing B] [IsLocalRing B]
    [Algebra S B] [Algebra R B] [IsScalarTower R S B]
    [IsDomain R] [IsIntegrallyClosed R] [Algebra.Etale R S]
    (M : Submonoid S) [IsLocalization M B] : IsDomain B := by
  let K := FractionRing R
  let T := B ⊗[R] K
  let N := Algebra.algebraMapSubmonoid B R⁰
  have : Module.Flat S B := IsLocalization.flat B M
  have : Module.Flat R B := Module.Flat.trans R S B
  have : Algebra.FormallyUnramified S B :=
    Algebra.FormallyUnramified.of_isLocalization M
  have : Algebra.FormallyUnramified R B := Algebra.FormallyUnramified.comp R S B
  have : Algebra.EssFiniteType S B := Algebra.EssFiniteType.of_isLocalization B M
  have : Algebra.EssFiniteType R B := Algebra.EssFiniteType.comp R S B
  have hN : N ≤ B⁰ := regular_image
  have : IsArtinianRing T := artinian_genericFiber
  have : IsFractionRing B T := IsLocalization.of_le N B⁰ hN fun a ha ↦
    IsArtinianRing.isUnit_of_mem_nonZeroDivisors
      (IsLocalization.nonZeroDivisors_le_comap N T ha)
  have : Algebra.FormallyUnramified K T :=
    Algebra.FormallyUnramified.of_equiv (Algebra.TensorProduct.commRight R K B)
  have : Algebra.EssFiniteType K T := Algebra.EssFiniteType.of_surjective
    (Algebra.TensorProduct.commRight R K B).toAlgHom
    (Algebra.TensorProduct.commRight R K B).surjective
  have : IsReduced T := Algebra.FormallyUnramified.isReduced_of_field K T
  have : IsIntegrallyClosed B := isIntegrallyClosed_of_etale_loc (R := R) M
  have : IsIntegrallyClosedIn B T :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn T).mp inferInstance
  exact isDomain_of_artinian_extension (A := B) (T := T)

end FrobeniusSplitting
