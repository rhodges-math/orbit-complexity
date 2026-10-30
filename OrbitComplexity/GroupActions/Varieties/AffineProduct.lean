import OrbitComplexity.GroupActions.Varieties.AffinePoints
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Points of affine products

The tensor-product description of an affine fiber product identifies its rational points
with pairs of rational points. This identification commutes with the two scheme projections.

## Main definitions

* `GroupActions.tensorAlgebraPointsEquiv`: tensor algebra points as pairs of algebra points.
* `GroupActions.affineProductPointsEquiv`: affine product sections as pairs of sections.

## Main results

* `GroupActions.affineProductPointsEquiv_pullback`: compatibility with the scheme fiber product.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u

variable (K A B : Type u) [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

/-- Points of a tensor product of commutative algebras are pairs of algebra points. -/
def tensorAlgebraPointsEquiv :
    (A ⊗[K] B →ₐ[K] K) ≃ (A →ₐ[K] K) × (B →ₐ[K] K) where
  toFun f := (f.comp Algebra.TensorProduct.includeLeft,
    f.comp Algebra.TensorProduct.includeRight)
  invFun p := Algebra.TensorProduct.lift p.1 p.2 (fun _ _ => .all _ _)
  left_inv f := by ext <;> simp
  right_inv p := by apply Prod.ext <;> ext <;> simp

/-- A tensor point attached to a pair evaluates pure tensors by multiplying their values. -/
@[simp]
theorem tensorAlgebraPointsEquiv_symm_tmul
    (p : (A →ₐ[K] K) × (B →ₐ[K] K)) (a : A) (b : B) :
    (tensorAlgebraPointsEquiv K A B).symm p (a ⊗ₜ[K] b) = p.1 a * p.2 b := rfl

/-- Sections of an affine tensor product are pairs of sections of its two affine factors. -/
def affineProductPointsEquiv :
    {p : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (A ⊗[K] B)) //
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A ⊗[K] B))) = 𝟙 _} ≃
    {p : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A) //
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) = 𝟙 _} ×
    {p : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of B) //
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) = 𝟙 _} :=
  affinePointsEquiv.symm.trans ((tensorAlgebraPointsEquiv K A B).trans
    (Equiv.prodCongr affinePointsEquiv affinePointsEquiv))

/-- The first factor point is obtained by the affine projection induced by the left inclusion. -/
theorem affineProductPointsEquiv_fst
    (p : {p : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (A ⊗[K] B)) //
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A ⊗[K] B))) = 𝟙 _}) :
    ((affineProductPointsEquiv K A B) p).1.val =
      p.val ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).toRingHom) := by
  obtain ⟨f, rfl⟩ := affinePointsEquiv.surjective p
  simp only [affineProductPointsEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.prodCongr_apply]
  change Spec.map (CommRingCat.ofHom
    (f.comp Algebra.TensorProduct.includeLeft).toRingHom) = _
  rw [affinePointsEquiv_apply, ← Spec.map_comp]
  rfl

/-- The second factor point is obtained by the affine projection induced by the right inclusion. -/
theorem affineProductPointsEquiv_snd
    (p : {p : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (A ⊗[K] B)) //
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A ⊗[K] B))) = 𝟙 _}) :
    ((affineProductPointsEquiv K A B) p).2.val =
      p.val ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).toRingHom) := by
  obtain ⟨f, rfl⟩ := affinePointsEquiv.surjective p
  simp only [affineProductPointsEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.prodCongr_apply]
  change Spec.map (CommRingCat.ofHom
    (f.comp Algebra.TensorProduct.includeRight).toRingHom) = _
  rw [affinePointsEquiv_apply, ← Spec.map_comp]
  rfl

/-- The paired section agrees with the canonical affine fiber-product isomorphism. -/
theorem affineProductPointsEquiv_pullback
    (p : {p : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (A ⊗[K] B)) //
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap K (A ⊗[K] B))) = 𝟙 _}) :
    p.val ≫ (pullbackSpecIso K A B).inv =
      pullback.lift ((affineProductPointsEquiv K A B) p).1.val
        ((affineProductPointsEquiv K A B) p).2.val
        (by rw [((affineProductPointsEquiv K A B) p).1.property,
          ((affineProductPointsEquiv K A B) p).2.property]) := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd,
      pullback.lift_fst, pullback.lift_snd, affineProductPointsEquiv_fst,
      affineProductPointsEquiv_snd] <;> rfl

end

end GroupActions
