import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.AffineScalarCoordinates

/-! # The same prior affine charts and their generic pullbacks -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u
namespace FrobeniusSplitting

/-- Restricting the prior-model comparison retains its affine tensor coordinates. -/
theorem exists_prior_patch_coordinates {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] {Y YK W : Scheme.{u}} [IsAffine W]
    (base : Y ⟶ Spec (.of R)) (baseK : YK ⟶ Spec (.of K)) (qY : YK ⟶ Y)
    (h : IsPullback qY baseK base (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (a : W ⟶ Y) :
    let P := (pullback a qY : Scheme.{u})
    let t := pullback.snd a qY ≫ baseK
    letI : Algebra R Γ(W, ⊤) :=
      ((a ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    letI : Algebra K Γ(P, ⊤) :=
      (t.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∃ e : K ⊗[R] Γ(W, ⊤) ≃ₐ[K] Γ(P, ⊤),
      (∀ k, e (k ⊗ₜ[R] (1 : Γ(W, ⊤))) = algebraMap K Γ(P, ⊤) k) ∧
      (∀ x, e ((1 : K) ⊗ₜ[R] x) = (pullback.fst a qY).appTop.hom x) ∧
      ∀ k x, e (k ⊗ₜ[R] x) =
        algebraMap K Γ(P, ⊤) k * (pullback.fst a qY).appTop.hom x :=
  exists_affine_scalar_coordinates (a ≫ base) (pullback.snd a qY ≫ baseK)
    (pullback.fst a qY) ((IsPullback.of_hasPullback a qY).paste_vert h)

end FrobeniusSplitting
