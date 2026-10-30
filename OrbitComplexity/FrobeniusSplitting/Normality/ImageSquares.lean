import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ImagePushouts
import OrbitComplexity.FrobeniusSplitting.Normality.RelativeModels

/-!
# Image Squares

Relative scalar comparisons identify pushout squares of model images.
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- Relative scalar comparisons and finite image generation give a cartesian affine model square. -/
theorem isPushout_of_relative_images {A B C Z E F G D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing Z]
    [CommRing E] [CommRing F] [CommRing G] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A Z] [Algebra A E]
    [Algebra E F] [Algebra E G] [Algebra E D] [Algebra A D]
    [Algebra A F] [Algebra A G]
    [IsScalarTower A E D] [Module.Flat A B] [Module.Flat A C]
    (p : B →ₐ[A] Z) (q : C →ₐ[A] Z) (ι : Z →ₐ[A] D)
    (eB : E ⊗[A] B ≃ₐ[E] F) (eC : E ⊗[A] C ≃ₐ[E] G)
    (eD : F ⊗[E] G ≃ₐ[E] D)
    (s : B →ₐ[A] F) (t : C →ₐ[A] G)
    (v : F →ₐ[E] D) (w : G →ₐ[E] D)
    (hB : ∀ b, eB ((1 : E) ⊗ₜ[A] b) = s b)
    (hC : ∀ c, eC ((1 : E) ⊗ₜ[A] c) = t c)
    (hD : ∀ f g, eD (f ⊗ₜ[E] g) = v f * w g)
    (hp : ∀ b, ι (p b) = v (s b)) (hq : ∀ c, ι (q c) = w (t c))
    (hi : Function.Injective (algebraMap A E)) (hgen : p.range ⊔ q.range = ⊤) :
    IsPushout (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (algebraMap A C)) (CommRingCat.ofHom p.toRingHom)
      (CommRingCat.ofHom q.toRingHom) := by
  let e : E ⊗[A] (B ⊗[A] C) ≃ₐ[E] D :=
    ((TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv A E B C).trans
      (Algebra.TensorProduct.congr eB eC)).trans eD
  have he (b : B) (c : C) :
      e ((1 : E) ⊗ₜ[A] (b ⊗ₜ[A] c)) = v (s b) * w (t c) := by
    change eD ((Algebra.TensorProduct.congr eB eC)
      (TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv A E B C
        ((1 : E) ⊗ₜ[A] (b ⊗ₜ[A] c)))) = _
    rw [TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv_tmul]
    change eD (eB ((1 : E) ⊗ₜ[A] b) ⊗ₜ[E] eC ((1 : E) ⊗ₜ[A] c)) = _
    rw [hB, hC, hD]
  apply isPushout_of_flat_images p q ι e hi hgen
  apply Algebra.TensorProduct.ext'
  intro b c
  change ι (p b * q c) = e ((1 : E) ⊗ₜ[A] (b ⊗ₜ[A] c))
  rw [map_mul, hp, hq, he]

end FrobeniusSplitting
