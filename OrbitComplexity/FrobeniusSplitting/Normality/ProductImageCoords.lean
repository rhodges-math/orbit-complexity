import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ProductImages
import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImageRanges

/-!
# ProductImageCoords

Fixed-fibre coefficient models and their arithmetic scheme comparisons.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

/-- Product coordinates with intrinsic base images identify the complete chart model
with the intrinsic image of its initial product model. -/
theorem exists_product_image_coords {S R K B A F N : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing B] [CommRing A] [CommRing F]
    [CommRing N] [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S B] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [Algebra R N] [Module.Flat ℤ F]
    (e : K ⊗[S] B ≃ₐ[K] A) (M : Subalgebra R A)
    (hM : M = Algebra.adjoin R (Set.range fun b : B ↦ e ((1 : K) ⊗ₜ[S] b)))
    (coords : N ≃ₐ[R] M ⊗[ℤ] F) (eval : N →ₐ[R] A ⊗[ℤ] F)
    (heval : ∀ z, Algebra.TensorProduct.map M.val (AlgHom.id ℤ F) (coords z) = eval z) :
    ∃ u : N ≃ₐ[R]
      (scalarImageHom (R := R) (tensorModelEquiv (S := ℤ) (B := F) e)).range,
      ∀ z, (u z : A ⊗[ℤ] F) = eval z := by
  have hM' : M = (scalarImageHom (R := R) e).range :=
    hM.trans (scalarImage_range (R := R) e).symm
  clear hM
  subst M
  refine ⟨coords.trans (productImageEquiv e), ?_⟩
  intro z
  exact (productImageEquiv_apply e (coords z)).trans (heval z)

end FrobeniusSplitting
