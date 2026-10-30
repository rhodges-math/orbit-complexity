import OrbitComplexity.FrobeniusSplitting.Normality.Retractions.ModelIsoFamily
import Mathlib.RingTheory.Flat.Basic

/-! Simultaneous comparison of models over nested coefficient rings. -/

open scoped TensorProduct

universe u v

namespace FrobeniusSplitting

private theorem cancel_generic_square {S T R K M : Type*}
    [CommRing S] [CommRing T] [CommRing R] [CommRing K] [CommRing M]
    [Algebra S T] [Algebra T R] [Algebra S R]
    [Algebra R K] [Algebra T K] [Algebra S K] [Algebra S M]
    [IsScalarTower S T R] [IsScalarTower T R K]
    [IsScalarTower S R K] [IsScalarTower S T K] (x : R ⊗[S] M) :
    Algebra.TensorProduct.cancelBaseChange S T K K M
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
        (AlgHom.id T (T ⊗[S] M))
        ((Algebra.TensorProduct.cancelBaseChange S T R R M).symm x)) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r m =>
    simp only [Algebra.TensorProduct.cancelBaseChange_symm_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem cancel_equiv_square {S T R K M N A : Type*}
    [CommRing S] [CommRing T] [CommRing R] [CommRing K]
    [CommRing M] [CommRing N] [CommRing A]
    [Algebra S T] [Algebra T R] [Algebra S R]
    [Algebra R K] [Algebra T K] [Algebra S K] [Algebra S M] [Algebra T N]
    [Algebra K A] [IsScalarTower S T R] [IsScalarTower T R K]
    [IsScalarTower S R K] [IsScalarTower S T K]
    (eM : K ⊗[S] M ≃ₐ[K] A) (eN : K ⊗[T] N ≃ₐ[K] A)
    (c : R ⊗[T] (T ⊗[S] M) ≃ₐ[R] R ⊗[S] M)
    (hc : c = Algebra.TensorProduct.cancelBaseChange S T R R M)
    (E : R ⊗[T] (T ⊗[S] M) ≃ₐ[R] R ⊗[T] N)
    (hE : ∀ y, eN (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
      (AlgHom.id T N) (E y)) =
        ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM)
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
            (AlgHom.id T (T ⊗[S] M)) y)) (x : R ⊗[S] M) :
    eN (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K) (AlgHom.id T N)
      (E (c.symm x))) =
      eM (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M) x) := by
  subst c
  have h := hE ((Algebra.TensorProduct.cancelBaseChange S T R R M).symm x)
  exact h.trans (congrArg eM (cancel_generic_square (T := T) x))

/-- Nested coefficient models can be compared jointly, retaining all original generic maps. -/
theorem exists_mixed_iso_family {K : Type u} [Field K]
    (S T : Subalgebra ℤ K) (hT : T.FG) (hST : S ≤ T)
    {I : Type v} [Finite I] (M N A : I → Type u)
    [∀ i, CommRing (M i)] [∀ i, CommRing (N i)] [∀ i, CommRing (A i)]
    [∀ i, Algebra S (M i)] [∀ i, Algebra T (N i)] [∀ i, Algebra K (A i)]
    [∀ i, Algebra.FinitePresentation S (M i)]
    [∀ i, Algebra.FinitePresentation T (N i)]
    (eM : ∀ i, K ⊗[S] M i ≃ₐ[K] A i)
    (eN : ∀ i, K ⊗[T] N i ≃ₐ[K] A i) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ ∃ hTR : T ≤ R,
      letI : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
      letI : Algebra S R := (Subalgebra.inclusion (hST.trans hTR)).toAlgebra
      letI : IsScalarTower T R K := Subalgebra.inclusion.isScalarTower_right hTR K
      letI : IsScalarTower S R K :=
        Subalgebra.inclusion.isScalarTower_right (hST.trans hTR) K
      ∀ i, ∃ E : R ⊗[S] M i ≃ₐ[R] R ⊗[T] N i, ∀ x,
        eN i (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
          (AlgHom.id T (N i)) (E x)) =
        eM i (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S (M i)) x) := by
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let e0 (i : I) : K ⊗[T] (T ⊗[S] M i) ≃ₐ[K] A i :=
    (Algebra.TensorProduct.cancelBaseChange S T K K (M i)).trans (eM i)
  obtain ⟨R, hR, hTR, hE⟩ := exists_model_iso_family T hT
    (fun i => T ⊗[S] M i) N A e0 eN
  let : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
  let : Algebra S R := (Subalgebra.inclusion (hST.trans hTR)).toAlgebra
  let : IsScalarTower T R K := Subalgebra.inclusion.isScalarTower_right hTR K
  let : IsScalarTower S R K :=
    Subalgebra.inclusion.isScalarTower_right (hST.trans hTR) K
  let : IsScalarTower S T R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨R, hR, hTR, ?_⟩
  intro i
  obtain ⟨E, hEi⟩ := hE i
  let c : R ⊗[T] (T ⊗[S] M i) ≃ₐ[R] R ⊗[S] M i :=
    Algebra.TensorProduct.cancelBaseChange S T R R (M i)
  refine ⟨c.symm.trans E, ?_⟩
  intro x
  have h := cancel_equiv_square (S := S) (T := T) (R := R) (K := K)
    (M := M i) (N := N i) (A := A i) (eM i) (eN i) c rfl E
  have hx := h hEi x
  change eN i (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
      (AlgHom.id T (N i)) (E (c.symm x))) =
    eM i (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
      (AlgHom.id S (M i)) x)
  exact hx

/-- A generic comparison with a flat target transports a retraction to the prescribed map. -/
theorem retraction_of_generic_square {R K M₀ N₀ M₁ N₁ : Type*}
    [CommRing R] [CommRing K] [Algebra R K]
    [CommRing M₀] [CommRing N₀] [CommRing M₁] [CommRing N₁]
    [Algebra R M₀] [Algebra R N₀] [Algebra R M₁] [Algebra R N₁]
    [Module.Flat R N₁] (hRK : Function.Injective (algebraMap R K))
    (f : M₀ →ₐ[R] N₀) (g : M₁ →ₐ[R] N₁)
    (eM : M₀ ≃ₐ[R] M₁) (eN : N₀ ≃ₐ[R] N₁)
    (r : N₁ →ₗ[R] M₁) (hr : r.comp g.toLinearMap = LinearMap.id)
    (hsq : ∀ x, (Algebra.TensorProduct.includeRight : N₁ →ₐ[R] K ⊗[R] N₁)
      (eN (f x)) = Algebra.TensorProduct.includeRight (g (eM x))) :
    ∃ r₀ : N₀ →ₗ[R] M₀, r₀.comp f.toLinearMap = LinearMap.id := by
  have hfg (x : M₀) : eN (f x) = g (eM x) :=
    Algebra.TensorProduct.includeRight_injective hRK (hsq x)
  refine ⟨eM.symm.toLinearMap.comp (r.comp eN.toLinearMap), ?_⟩
  apply LinearMap.ext
  intro x
  change eM.symm (r (eN (f x))) = x
  rw [hfg]
  have h := LinearMap.congr_fun hr (eM x)
  change r (g (eM x)) = eM x at h
  rw [h, eM.symm_apply_apply]

end FrobeniusSplitting
