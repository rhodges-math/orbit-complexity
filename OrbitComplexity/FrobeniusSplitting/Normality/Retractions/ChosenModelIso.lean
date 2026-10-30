import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.FreePair
import OrbitComplexity.FrobeniusSplitting.Normality.Retractions.FreeModelIso

/-! Synchronization of prescribed arithmetic models with their original generic comparisons. -/

open TensorProduct

namespace FrobeniusSplitting

private theorem model_image_cancel {S T R K M A : Type*}
    [CommRing S] [CommRing T] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S T] [Algebra S R] [Algebra T R] [IsScalarTower S T R]
    [Algebra S K] [Algebra T K] [Algebra R K]
    [IsScalarTower S T K] [IsScalarTower S R K] [IsScalarTower T R K]
    [Algebra S M] [Algebra K A] (e : K ⊗[S] M ≃ₐ[K] A)
    (x : R ⊗[T] (T ⊗[S] M)) :
    e (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M)
      (Algebra.TensorProduct.cancelBaseChange S T R R M x)) =
    ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans e)
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
        (AlgHom.id T (T ⊗[S] M)) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r y =>
      induction y using TensorProduct.inductionOn with
      | tmul t m =>
          simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.cancelBaseChange_tmul,
            Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
          change e ((algebraMap R K (t • r)) ⊗ₜ[S] m) =
            e ((t • algebraMap R K r) ⊗ₜ[S] m)
          apply congrArg (fun k : K => e (k ⊗ₜ[S] m))
          simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply T R K]
      | add y z hy hz =>
          simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hy hz
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private theorem model_iso_cancel {S T R K M₀ M₁ A : Type*}
    [CommRing S] [CommRing T] [CommRing R] [CommRing K]
    [CommRing M₀] [CommRing M₁] [CommRing A]
    [Algebra S T] [Algebra S R] [Algebra T R] [IsScalarTower S T R]
    [Algebra S K] [Algebra T K] [Algebra R K]
    [IsScalarTower S T K] [IsScalarTower S R K] [IsScalarTower T R K]
    [Algebra S M₀] [Algebra S M₁] [Algebra K A]
    (e₀ : K ⊗[S] M₀ ≃ₐ[K] A) (e₁ : K ⊗[S] M₁ ≃ₐ[K] A)
    (E : R ⊗[T] (T ⊗[S] M₀) ≃ₐ[R] R ⊗[T] (T ⊗[S] M₁))
    (hE : ∀ x,
      ((Algebra.TensorProduct.cancelBaseChange S T K K M₁).trans e₁)
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
          (AlgHom.id T (T ⊗[S] M₁)) (E x)) =
      ((Algebra.TensorProduct.cancelBaseChange S T K K M₀).trans e₀)
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
          (AlgHom.id T (T ⊗[S] M₀)) x)) :
    ∃ E' : R ⊗[S] M₀ ≃ₐ[R] R ⊗[S] M₁, ∀ x,
      e₁ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M₁) (E' x)) =
      e₀ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M₀) x) := by
  let c₀ := Algebra.TensorProduct.cancelBaseChange S T R R M₀
  let c₁ := Algebra.TensorProduct.cancelBaseChange S T R R M₁
  refine ⟨c₀.symm.trans (E.trans c₁), fun x => ?_⟩
  have h₁ := model_image_cancel e₁ (E (c₀.symm x))
  have h₀ := model_image_cancel e₀ (c₀.symm x)
  exact h₁.trans ((hE (c₀.symm x)).trans (h₀.symm.trans
    (congrArg (fun z => e₀ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
      (AlgHom.id S M₀) z)) (c₀.apply_symm_apply x))))

universe u

private theorem chosen_iso_of_free {K M₀ M₁ A : Type u} [Field K]
    [CommRing M₀] [CommRing M₁] [CommRing A] [Algebra K A]
    (S T : Subalgebra ℤ K) (hT : T.FG) (hST : S ≤ T)
    [Algebra S M₀] [Algebra S M₁]
    [Algebra.FinitePresentation S M₀] [Algebra.FinitePresentation S M₁]
    (e₀ : K ⊗[S] M₀ ≃ₐ[K] A) (e₁ : K ⊗[S] M₁ ≃ₐ[K] A)
    (hfree₀ : letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      Module.Free T (T ⊗[S] M₀))
    (hfree₁ : letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      Module.Free T (T ⊗[S] M₁)) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ ∃ hSR : S ≤ R,
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      ∃ E : R ⊗[S] M₀ ≃ₐ[R] R ⊗[S] M₁, ∀ x,
        e₁ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S M₁) (E x)) =
        e₀ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S M₀) x) := by
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  have : Module.Free T (T ⊗[S] M₀) := hfree₀
  have : Module.Free T (T ⊗[S] M₁) := hfree₁
  let eT₀ := (Algebra.TensorProduct.cancelBaseChange S T K K M₀).trans e₀
  let eT₁ := (Algebra.TensorProduct.cancelBaseChange S T K K M₁).trans e₁
  have : Algebra.FinitePresentation T (T ⊗[S] M₀) := inferInstance
  have : Algebra.FinitePresentation T (T ⊗[S] M₁) := inferInstance
  obtain ⟨R, hR, hTR, E, hE⟩ := exists_free_model_iso (K := K)
    (M₀ := T ⊗[S] M₀) (M₁ := T ⊗[S] M₁) (A := A) T hT eT₀ eT₁
  let : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
  let : IsScalarTower T R K := Subalgebra.inclusion.isScalarTower_right hTR K
  have hSR : S ≤ R := hST.trans hTR
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  have : IsScalarTower S T R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨R, hR, hSR, model_iso_cancel (S := S) (T := T) (R := R) (K := K)
    (M₀ := M₀) (M₁ := M₁) (A := A) e₀ e₁ E hE⟩

/-- Two prescribed models of the same generic algebra agree after one coefficient enlargement. -/
theorem exists_chosen_model_iso {K M₀ M₁ A : Type u} [Field K]
    [CommRing M₀] [CommRing M₁] [CommRing A] [Algebra K A]
    (S : Subalgebra ℤ K) (hS : S.FG) [Algebra S M₀] [Algebra S M₁]
    [Algebra.FinitePresentation S M₀] [Algebra.FinitePresentation S M₁]
    (e₀ : K ⊗[S] M₀ ≃ₐ[K] A) (e₁ : K ⊗[S] M₁ ≃ₐ[K] A) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ ∃ hSR : S ≤ R,
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      ∃ E : R ⊗[S] M₀ ≃ₐ[R] R ⊗[S] M₁, ∀ x,
        e₁ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S M₁) (E x)) =
        e₀ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S M₀) x) := by
  obtain ⟨T, hT, hST, hfree₀, hfree₁⟩ := exists_free_pair_models (A := M₀) (B := M₁) S hS
  exact chosen_iso_of_free S T hT hST e₀ e₁ hfree₀ hfree₁

end FrobeniusSplitting
