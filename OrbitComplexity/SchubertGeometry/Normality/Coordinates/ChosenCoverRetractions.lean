import OrbitComplexity.SchubertGeometry.Normality.Coordinates.ChosenCoverCoordinates
import OrbitComplexity.SchubertGeometry.Normality.Coordinates.EndpointProducts

/-! # Retractions of the prescribed endpoint cover map

The source, target, endpoint and affine source cover are the specified models.
Their original Cartesian comparisons prove generic injectivity of this model
map itself. A coefficient enlargement therefore splits this same map, without
choosing a second endpoint map on its coordinate rings.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace SchubertGeometry

noncomputable section

universe u

/-- The specified cover-section map of the prescribed endpoint has a retraction
after coefficient enlargement. All source and target coordinate rings and the
map being split are the scalar extensions of those specified in the input. -/
theorem exists_chosen_cover_retractions {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG)
    {X₀ Y₀ X Y : Scheme.{u}} [IsAffine Y₀]
    (x₀ : X₀ ⟶ Spec (.of S)) (y₀ : Y₀ ⟶ Spec (.of S))
    (x : X ⟶ Spec (.of K)) (y : Y ⟶ Spec (.of K))
    (f₀ : X₀ ⟶ Y₀) (f : X ⟶ Y)
    (hf₀ : f₀ ≫ y₀ = x₀) (hfK : f ≫ y = x)
    [QuasiCompact f] [Surjective f] [IsReduced Y]
    (qX : X ⟶ X₀) (qY : Y ⟶ Y₀)
    (hX : IsPullback qX x x₀
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY y y₀
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hf : f ≫ qY = qX ≫ f₀)
    (V : X₀.OpenCover.{u}) [Finite V.I₀]
    (hV : ∀ j, IsAffine (V.X j))
    [Algebra.FinitePresentation S ((algΓ (.of S)).obj (Over.mk y₀)).unop]
    [∀ j, Algebra.FinitePresentation S
      ((algΓ (.of S)).obj (Over.mk (V.f j ≫ x₀))).unop] :
    let M : Type u := ((algΓ (.of S)).obj (Over.mk y₀)).unop
    let N (j : V.I₀) : Type u :=
      ((algΓ (.of S)).obj (Over.mk (V.f j ≫ x₀))).unop
    let g₀ := affineCoverSectionMap
      (Over.homMk f₀ hf₀ : Over.mk x₀ ⟶ Over.mk y₀) V
    ∃ (R : Subalgebra ℤ K), R.FG ∧ ∃ hSR : S ≤ R,
      let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      ∃ r : R ⊗[S] (∀ j, N j) →ₗ[R] R ⊗[S] M,
        r.comp (Algebra.TensorProduct.lTensor (S := R) R g₀).toLinearMap =
          LinearMap.id := by
  let M : Type u := ((algΓ (.of S)).obj (Over.mk y₀)).unop
  let N (j : V.I₀) : Type u :=
    ((algΓ (.of S)).obj (Over.mk (V.f j ≫ x₀))).unop
  let g₀ : M →ₐ[S] ∀ j, N j := affineCoverSectionMap
    (Over.homMk f₀ hf₀ : Over.mk x₀ ⟶ Over.mk y₀) V
  let : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have hft : Algebra.FiniteType S (∀ j, N j) := finiteType_pi S V.I₀ N
  let : Algebra.FinitePresentation S (∀ j, N j) :=
    Algebra.FinitePresentation.of_finiteType.mp hft
  have hinj : Function.Injective (Algebra.TensorProduct.lTensor (S := K) K g₀) :=
    chosen_cover_tensor_injective x₀ y₀ x y f₀ f hf₀ hfK qX qY hX hY hf V hV
  exact exists_injective_image_model S hS g₀ hinj

end
end SchubertGeometry
