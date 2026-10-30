import OrbitComplexity.FrobeniusSplitting.Normality.Retractions.ChosenModelIso

/-! Simultaneous comparisons of finite families of coefficient models. -/

open TensorProduct

namespace FrobeniusSplitting

private theorem image_cancel_smul {S T R K M A : Type*}
    [CommRing S] [CommRing T] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S T] [Algebra S R] [Algebra T R] [IsScalarTower S T R]
    [Algebra S K] [Algebra T K] [Algebra R K]
    [IsScalarTower S T K] [IsScalarTower S R K] [IsScalarTower T R K]
    [Algebra S M] [Algebra K A] (e : K ⊗[S] M ≃ₐ[K] A)
    (r : R) (x : T ⊗[S] M) :
    e (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M)
      (Algebra.TensorProduct.cancelBaseChange S T R R M (r ⊗ₜ[T] x))) =
      algebraMap R K r • e
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K) (AlgHom.id S M) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t m =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.cancelBaseChange_tmul]
      change e ((algebraMap R K (t • r)) ⊗ₜ[S] m) =
        algebraMap R K r • e ((algebraMap T K t) ⊗ₜ[S] m)
      rw [← map_smul e]
      apply congrArg e
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply T R K,
        smul_tmul', smul_eq_mul, mul_comm]
  | add x y hx hy =>
      simpa only [tmul_add, map_add, smul_add] using congrArg₂ (· + ·) hx hy

private theorem extend_model_iso {S T R K M₀ M₁ A : Type*}
    [CommRing S] [CommRing T] [CommRing R] [CommRing K]
    [CommRing M₀] [CommRing M₁] [CommRing A]
    [Algebra S T] [Algebra S R] [Algebra T R] [IsScalarTower S T R]
    [Algebra S K] [Algebra T K] [Algebra R K]
    [IsScalarTower S T K] [IsScalarTower S R K] [IsScalarTower T R K]
    [Algebra S M₀] [Algebra S M₁] [Algebra K A]
    (e₀ : K ⊗[S] M₀ ≃ₐ[K] A) (e₁ : K ⊗[S] M₁ ≃ₐ[K] A)
    (E : T ⊗[S] M₀ ≃ₐ[T] T ⊗[S] M₁)
    (hE : ∀ x,
      e₁ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K) (AlgHom.id S M₁) (E x)) =
      e₀ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K) (AlgHom.id S M₀) x)) :
    ∃ E' : R ⊗[S] M₀ ≃ₐ[R] R ⊗[S] M₁, ∀ x,
      e₁ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M₁) (E' x)) =
      e₀ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M₀) x) := by
  let c₀ := Algebra.TensorProduct.cancelBaseChange S T R R M₀
  let c₁ := Algebra.TensorProduct.cancelBaseChange S T R R M₁
  let d : R ⊗[T] (T ⊗[S] M₀) ≃ₐ[R] R ⊗[T] (T ⊗[S] M₁) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) E
  let F := c₀.symm.trans (d.trans c₁)
  refine ⟨F, fun x => ?_⟩
  induction x using TensorProduct.inductionOn with
  | tmul r m =>
      simp only [F, c₀, AlgEquiv.trans_apply,
        Algebra.TensorProduct.cancelBaseChange_symm_tmul, d,
        Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      change e₁ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M₁)
        (c₁ (r ⊗ₜ[T] E ((1 : T) ⊗ₜ[S] m)))) =
        e₀ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M₀)
          (r ⊗ₜ[S] m))
      rw [image_cancel_smul (S := S) (T := T) (R := R) (K := K) e₁, hE]
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
      change algebraMap R K r • e₀ ((1 : K) ⊗ₜ[S] m) =
        e₀ ((algebraMap R K r) ⊗ₜ[S] m)
      rw [← map_smul e₀, smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

universe u v

/-- Finite families of prescribed models agree over one finitely generated coefficient ring. -/
theorem exists_model_iso_family {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {I : Type v} [Finite I]
    (M₀ M₁ A : I → Type u)
    [∀ i, CommRing (M₀ i)] [∀ i, CommRing (M₁ i)] [∀ i, CommRing (A i)]
    [∀ i, Algebra S (M₀ i)] [∀ i, Algebra S (M₁ i)] [∀ i, Algebra K (A i)]
    [∀ i, Algebra.FinitePresentation S (M₀ i)]
    [∀ i, Algebra.FinitePresentation S (M₁ i)]
    (e₀ : ∀ i, K ⊗[S] M₀ i ≃ₐ[K] A i)
    (e₁ : ∀ i, K ⊗[S] M₁ i ≃ₐ[K] A i) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ ∃ hSR : S ≤ R,
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      ∀ i, ∃ E : R ⊗[S] M₀ i ≃ₐ[R] R ⊗[S] M₁ i, ∀ x,
        e₁ i (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S (M₁ i)) (E x)) =
        e₀ i (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S (M₀ i)) x) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  choose T hT hST E hE using fun i => exists_chosen_model_iso S hS (e₀ i) (e₁ i)
  have hfg (s : Finset I) : (s.sup T).FG := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sup_empty] using (Subalgebra.fg_bot :
        (⊥ : Subalgebra ℤ K).FG)
    | @insert i s hi ih => simpa only [Finset.sup_insert] using (hT i).sup ih
  let R : Subalgebra ℤ K := S ⊔ Finset.univ.sup T
  have hR : R.FG := hS.sup (hfg Finset.univ)
  have hSR : S ≤ R := le_sup_left
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  refine ⟨R, hR, hSR, fun i => ?_⟩
  have hTR : T i ≤ R := le_sup_of_le_right (Finset.le_sup (Finset.mem_univ i))
  let : Algebra S (T i) := (Subalgebra.inclusion (hST i)).toAlgebra
  let : IsScalarTower S (T i) K := Subalgebra.inclusion.isScalarTower_right (hST i) K
  let : Algebra (T i) R := (Subalgebra.inclusion hTR).toAlgebra
  let : IsScalarTower (T i) R K := Subalgebra.inclusion.isScalarTower_right hTR K
  have : IsScalarTower S (T i) R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact extend_model_iso (S := S) (T := T i) (R := R) (K := K)
    (M₀ := M₀ i) (M₁ := M₁ i) (A := A i) (e₀ i) (e₁ i) (E i) (hE i)

end FrobeniusSplitting
