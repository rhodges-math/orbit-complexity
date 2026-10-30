import OrbitComplexity.FrobeniusSplitting.Modules.PolynomialImage
import OrbitComplexity.FrobeniusSplitting.Normality.TensorCoordinates

/-! # Mixed coefficient and polynomial Frobenius images -/

open Polynomial
open scoped TensorProduct
noncomputable section
universe u

namespace FrobeniusSplitting

variable (A : Type u) [CommRing A] (p : ℕ) [ExpChar A p]

private abbrev imageA := (frobenius A p).range
private abbrev imageB := (frobenius (Polynomial A) p).range

private def coefficientImage : imageA A p →+* imageB A p :=
  ((Polynomial.C : A →+* Polynomial A).comp (imageA A p).subtype).codRestrict
    (imageB A p) (by
      intro a
      obtain ⟨r, hr⟩ := a.property
      change r ^ p = a.val at hr
      refine ⟨C r, ?_⟩
      change (C r) ^ p = C a.val
      rw [← map_pow, hr])

private instance baseAlgebra : Algebra (imageA A p) A :=
  (imageA A p).subtype.toAlgebra

private instance imageAlgebra : Algebra (imageA A p) (imageB A p) :=
  (coefficientImage A p).toAlgebra

private def imageInclusion : imageB A p →ₐ[imageA A p] Polynomial A where
  __ := (imageB A p).subtype
  commutes' _ := rfl

private def powerImage : Polynomial (imageA A p) →ₐ[imageA A p] imageB A p where
  __ := (polynomialPowerMap A p).codRestrict (imageB A p) (by
    intro f
    change polynomialPowerMap A p f ∈ (frobenius (Polynomial A) p).range
    rw [← polynomialPowerMap_range]
    exact ⟨f, rfl⟩)
  commutes' a := by
    apply Subtype.ext
    change polynomialPowerMap A p (C a) = C a.val
    simp [polynomialPowerMap]

private theorem powerImage_bijective : Function.Bijective (powerImage A p) := by
  constructor
  · intro f g h
    exact polynomialPowerMap_injective A p (congrArg Subtype.val h)
  · intro b
    have hb : b.val ∈ (polynomialPowerMap A p).range := by
      rw [polynomialPowerMap_range]
      exact b.property
    obtain ⟨f, hf⟩ := hb
    exact ⟨f, Subtype.ext hf⟩

private def imageEquiv : Polynomial (imageA A p) ≃ₐ[imageA A p] imageB A p :=
  AlgEquiv.ofBijective (powerImage A p) (powerImage_bijective A p)

/-- Tensor multiplication includes the mixed image into the polynomial algebra. -/
def mixedPolynomialMap : A ⊗[imageA A p] imageB A p →ₐ[A] Polynomial A :=
  AlgHom.liftEquiv (imageA A p) A (imageB A p) (Polynomial A) (imageInclusion A p)

/-- Extending the polynomial Frobenius image from A^p to A retains ordinary coefficients. -/
def mixedPolynomialEquiv : A ⊗[imageA A p] imageB A p ≃ₐ[A] Polynomial A :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) (imageEquiv A p).symm).trans
    (polynomialTensorEquiv (imageA A p) A)

private theorem imageEquiv_power (f : Polynomial A) :
    (imageEquiv A p).symm ((frobenius (Polynomial A) p).rangeRestrict f) =
      Polynomial.map (frobenius A p).rangeRestrict f := by
  apply (imageEquiv A p).injective
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  change f ^ p = Polynomial.expand A p
    (Polynomial.map (imageA A p).subtype
      (Polynomial.map (frobenius A p).rangeRestrict f))
  rw [Polynomial.map_map]
  change f ^ p = Polynomial.expand A p (Polynomial.map (frobenius A p) f)
  rw [← Polynomial.map_expand, Polynomial.map_frobenius_expand]

private theorem mixed_equiv_power (a : A) (f : Polynomial A) :
    mixedPolynomialEquiv A p (a ⊗ₜ[imageA A p]
      ((frobenius (Polynomial A) p).rangeRestrict f)) =
      C a * Polynomial.map (frobenius A p) f := by
  change polynomialTensorEquiv (imageA A p) A
    (a ⊗ₜ[imageA A p] (imageEquiv A p).symm
      ((frobenius (Polynomial A) p).rangeRestrict f)) = _
  rw [imageEquiv_power, polynomialTensorEquiv_tmul, Polynomial.map_map]
  rfl

private theorem mixed_map_power (a : A) (f : Polynomial A) :
    mixedPolynomialMap A p (a ⊗ₜ[imageA A p]
      ((frobenius (Polynomial A) p).rangeRestrict f)) = C a * f ^ p := by
  unfold mixedPolynomialMap
  rw [AlgHom.liftEquiv_tmul, Algebra.smul_def]
  rfl

private theorem mixed_map_equation : mixedPolynomialMap A p =
    (Polynomial.expand A p).comp (mixedPolynomialEquiv A p).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro a b
  obtain ⟨f, rfl⟩ := (frobenius (Polynomial A) p).rangeRestrict_surjective b
  change mixedPolynomialMap A p
    (a ⊗ₜ[imageA A p] ((frobenius (Polynomial A) p).rangeRestrict f)) =
      Polynomial.expand A p (mixedPolynomialEquiv A p
        (a ⊗ₜ[imageA A p] ((frobenius (Polynomial A) p).rangeRestrict f)))
  rw [mixed_map_power, mixed_equiv_power, map_mul, Polynomial.expand_C]
  rw [← Polynomial.map_expand, Polynomial.map_frobenius_expand]

/-- Mixed image coordinates preserve input coefficients, and multiplication is the injective
relative expansion with precisely its image subring. -/
theorem mixedPolynomial_spec :
    (∀ (a : A) (f : Polynomial A),
      mixedPolynomialEquiv A p
        (a ⊗ₜ[imageA A p] ((frobenius (Polynomial A) p).rangeRestrict f)) =
          C a * Polynomial.map (frobenius A p) f) ∧
    (mixedPolynomialMap A p).toRingHom =
      (Polynomial.expand A p).toRingHom.comp (mixedPolynomialEquiv A p).toRingHom ∧
    Function.Injective (mixedPolynomialMap A p) ∧
    (mixedPolynomialMap A p).toRingHom.range = (Polynomial.expand A p).toRingHom.range := by
  have he : (mixedPolynomialMap A p).toRingHom =
      (Polynomial.expand A p).toRingHom.comp (mixedPolynomialEquiv A p).toRingHom :=
    congrArg AlgHom.toRingHom (mixed_map_equation A p)
  refine ⟨mixed_equiv_power A p, he, ?_, ?_⟩
  · intro x y h
    apply (mixedPolynomialEquiv A p).injective
    apply Polynomial.expand_injective (expChar_pos A p)
    have hx := congrArg (fun f => f x) (mixed_map_equation A p)
    have hy := congrArg (fun f => f y) (mixed_map_equation A p)
    exact hx.symm.trans (h.trans hy)
  · rw [he]
    ext b
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨mixedPolynomialEquiv A p m, rfl⟩
    · rintro ⟨f, rfl⟩
      refine ⟨(mixedPolynomialEquiv A p).symm f, ?_⟩
      change Polynomial.expand A p
        (mixedPolynomialEquiv A p ((mixedPolynomialEquiv A p).symm f)) = _
      rw [AlgEquiv.apply_symm_apply]
      rfl

end FrobeniusSplitting
