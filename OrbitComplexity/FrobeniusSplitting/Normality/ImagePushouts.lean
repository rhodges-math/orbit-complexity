import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ModelFlat
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Image Pushouts

Flat image algebras with generating images form pushout squares.
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- A generically identified image square of flat algebras is a pushout when its images generate. -/
theorem isPushout_of_flat_images {A B C D₀ : Type u} {E D : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D₀] [CommRing E] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D₀] [Algebra A E]
    [Algebra E D] [Algebra A D] [IsScalarTower A E D]
    [Module.Flat A B] [Module.Flat A C]
    (p : B →ₐ[A] D₀) (q : C →ₐ[A] D₀) (ι : D₀ →ₐ[A] D)
    (e : E ⊗[A] (B ⊗[A] C) ≃ₐ[E] D)
    (hi : Function.Injective (algebraMap A E))
    (hgen : p.range ⊔ q.range = ⊤)
    (hcomp : ι.comp (Algebra.TensorProduct.productMap p q) = tensorImageHom e) :
    IsPushout (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (algebraMap A C)) (CommRingCat.ofHom p.toRingHom)
      (CommRingCat.ofHom q.toRingHom) := by
  let φ := Algebra.TensorProduct.productMap p q
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      apply tensorImageHom_injective e hi
      have hx := AlgHom.congr_fun hcomp x
      have hy := AlgHom.congr_fun hcomp y
      exact hx.symm.trans ((congrArg ι hxy).trans hy)
    · apply (AlgHom.range_eq_top φ).mp
      rw [Algebra.TensorProduct.productMap_range, hgen]
  let e₀ : B ⊗[A] C ≃ₐ[A] D₀ := AlgEquiv.ofBijective φ hφ
  exact (CommRingCat.isPushout_tensorProduct A B C).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e₀.toRingEquiv.toCommRingCatIso
    (by simp) (by simp)
    (by ext b; exact Algebra.TensorProduct.productMap_left_apply p q b)
    (by ext c; exact Algebra.TensorProduct.productMap_right_apply p q c)

end FrobeniusSplitting
