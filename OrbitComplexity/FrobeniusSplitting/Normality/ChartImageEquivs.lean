import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ProductImageCoords
import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImageEquivs

/-!
# ChartImageEquivs

Fixed-fibre coefficient models and their arithmetic scheme comparisons.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

/-- Retained product coordinates identify a chart model with the intrinsic image
of the initial chart model in its generic coordinates. -/
theorem exists_chart_image_equiv {S R K B A F N D : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing B] [CommRing A] [CommRing F]
    [CommRing N] [CommRing D]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S B] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [Algebra R N] [Algebra K D] [Algebra R D] [IsScalarTower R K D]
    [Module.Flat ℤ F] (e : K ⊗[S] B ≃ₐ[K] A) (M : Subalgebra R A)
    (hM : M = Algebra.adjoin R (Set.range fun b : B ↦ e ((1 : K) ⊗ₜ[S] b)))
    (coords : N ≃ₐ[R] M ⊗[ℤ] F) (generic : D ≃ₐ[K] A ⊗[ℤ] F)
    (eval : N →ₐ[R] D)
    (heval : ∀ z, Algebra.TensorProduct.map M.val (AlgHom.id ℤ F) (coords z) =
      generic (eval z)) :
    ∃ u : N ≃ₐ[R] (scalarImageHom (R := R)
      ((tensorModelEquiv (S := ℤ) (B := F) e).trans generic.symm)).range,
      ∀ z, (u z : D) = eval z := by
  let eP := tensorModelEquiv (S := ℤ) (B := F) e
  let d := eP.trans generic.symm
  obtain ⟨uP, huP⟩ := exists_product_image_coords e M hM coords
    ((generic.restrictScalars R).toAlgHom.comp eval) heval
  let : Algebra S D := ((algebraMap K D).comp (algebraMap S K)).toAlgebra
  have : IsScalarTower S K D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let a := AlgEquiv.refl (R := S) (A₁ := B ⊗[ℤ] F)
  have h : generic.symm.toAlgHom.comp eP.toAlgHom =
      d.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K a.toAlgHom) := by
    apply Algebra.TensorProduct.ext'
    intro k x
    rfl
  let v := scalarImageEquiv (R := R) eP d a generic.symm h
  refine ⟨uP.trans v, ?_⟩
  intro z
  change (v (uP z) : D) = eval z
  rw [scalarImageEquiv_apply, huP]
  exact generic.symm_apply_apply (eval z)

end FrobeniusSplitting
