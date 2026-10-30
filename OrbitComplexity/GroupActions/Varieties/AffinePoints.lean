import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.MvPolynomial.Basic

/-! # Points of affine charts

Morphisms from the spectrum of a base ring into an affine scheme over that ring
are algebra homomorphisms into the base ring. For a polynomial ring, these morphisms
are determined by their coordinate values.

## Main definitions

* `GroupActions.affinePointsEquiv`: algebra homomorphisms as sections of an affine scheme.
* `GroupActions.affineSpacePointsEquiv`: coordinates of a point of affine space.

## Main results

* `GroupActions.affinePointsEquiv_apply`: the section attached to an algebra homomorphism.

## Implementation notes

The base ring and the affine coordinate ring belong to the same universe.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

universe u

variable {K R : Type u} [CommRing K] [CommRing R] [Algebra K R]

/-- Algebra homomorphisms into the base ring are sections of the affine structure morphism. -/
noncomputable def affinePointsEquiv :
    (R →ₐ[K] K) ≃
      {p : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) //
        p ≫ Spec.map (CommRingCat.ofHom (algebraMap K R)) = 𝟙 _} where
  toFun f := ⟨Spec.map (CommRingCat.ofHom f.toRingHom), by
    rw [← Spec.map_comp]
    have hf : CommRingCat.ofHom (algebraMap K R) ≫ CommRingCat.ofHom f.toRingHom =
        𝟙 (CommRingCat.of K) := by
      ext r
      exact f.commutes r
    rw [hf]
    exact Scheme.Spec.map_id _⟩
  invFun p :=
    { (Spec.preimage p.val).hom with
      commutes' := fun r => by
        have hp := congrArg Spec.preimage p.property
        rw [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id] at hp
        exact ConcreteCategory.congr_hom hp r }
  left_inv f := by
    ext r
    change (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom))).hom r = f r
    rw [Spec.preimage_map]
    rfl
  right_inv p := by
    apply Subtype.ext
    exact Spec.map_preimage p.val

/-- The section associated to an algebra homomorphism is its spectrum morphism. -/
theorem affinePointsEquiv_apply (f : R →ₐ[K] K) :
    (affinePointsEquiv f).val = Spec.map (CommRingCat.ofHom f.toRingHom) := rfl

variable (ι : Type u)

/-- Points of affine space over a ring are tuples of elements of that ring. -/
noncomputable def affineSpacePointsEquiv :
    {p : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (MvPolynomial ι K)) //
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial ι K))) = 𝟙 _} ≃
      (ι → K) :=
  affinePointsEquiv.symm.trans
    { toFun := fun f i => f (MvPolynomial.X i)
      invFun := MvPolynomial.aeval
      left_inv := fun f => MvPolynomial.algHom_ext fun i =>
        MvPolynomial.aeval_X (fun j => f (MvPolynomial.X j)) i
      right_inv := fun v => funext fun i => MvPolynomial.aeval_X v i }

section Field

variable {L A : Type u} [Field L] [CommRing A] [Algebra L A]

/-- The scheme point of an affine rational point is the prime ideal given by its kernel. -/
theorem affinePointsEquiv_prime (f : A →ₐ[L] L) :
    (affinePointsEquiv f).val (IsLocalRing.closedPoint L) =
      (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum A) := by
  apply PrimeSpectrum.ext
  change Ideal.comap f.toRingHom (IsLocalRing.maximalIdeal L) = RingHom.ker f
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

end Field

end GroupActions
