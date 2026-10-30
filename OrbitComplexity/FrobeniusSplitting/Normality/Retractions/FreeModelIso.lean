import OrbitComplexity.FrobeniusSplitting.Normality.Images.ChosenGraph
import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.GenericRegular
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Comparison of two free arithmetic models of the same generic algebra. -/

open TensorProduct

namespace FrobeniusSplitting

universe u

/-- Free arithmetic models of the same generic algebra agree after enlarging coefficients. -/
theorem exists_free_model_iso {K M₀ M₁ A : Type u} [Field K]
    [CommRing M₀] [CommRing M₁] [CommRing A] [Algebra K A]
    (S : Subalgebra ℤ K) (hS : S.FG) [Algebra S M₀] [Algebra S M₁]
    [Algebra.FinitePresentation S M₀] [Algebra.FinitePresentation S M₁]
    [Module.Free S M₀] [Module.Free S M₁]
    (e₀ : K ⊗[S] M₀ ≃ₐ[K] A) (e₁ : K ⊗[S] M₁ ≃ₐ[K] A) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ ∃ hSR : S ≤ R,
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      ∃ E : R ⊗[S] M₀ ≃ₐ[R] R ⊗[S] M₁, ∀ x,
        e₁ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S M₁) (E x)) =
        e₀ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S M₀) x) := by
  classical
  let M (b : Bool) : Type u := if b then M₁ else M₀
  let instM (b : Bool) : CommRing (M b) := by cases b <;> dsimp [M] <;> infer_instance
  let instSM (b : Bool) : Algebra S (M b) := by cases b <;> dsimp [M] <;> infer_instance
  let instFP (b : Bool) : Algebra.FinitePresentation S (M b) := by
    cases b <;> dsimp [M] <;> infer_instance
  let instFree (b : Bool) : Module.Free S (M b) := by
    cases b <;> dsimp [M] <;> infer_instance
  let e (b : Bool) : K ⊗[S] M b ≃ₐ[K] A := by
    cases b
    · exact e₀
    · exact e₁
  choose n k hQ using fun b => Algebra.Presentation.exists_presentation_fin S (M b)
  let Q b := (hQ b).some
  obtain ⟨R, hSR, F, hR, hF, _⟩ := exists_chosen_graph_elements S hS M
    (fun _ => A) e (fun b => Fin (n b)) (fun b => Fin (k b)) Q
    id Bool.not (fun _ => AlgHom.id K A) (fun _ => PEmpty.{1})
    (fun _ j => PEmpty.elim j)
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let : Algebra R A := ((algebraMap K A).comp R.val.toRingHom).toAlgebra
  let : SMul R A := (inferInstance : Algebra R A).toSMul
  have : IsScalarTower R K A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eR (b : Bool) : K ⊗[R] (R ⊗[S] M b) ≃ₐ[K] A :=
    (Algebra.TensorProduct.cancelBaseChange S R K K (M b)).trans (e b)
  let ev (b : Bool) := tensorImageHom (eR b)
  have hev (b : Bool) (x : R ⊗[S] M b) :
      ev b x = e b (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
        (AlgHom.id S (M b)) x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r m =>
        change e b ((Algebra.TensorProduct.cancelBaseChange S R K K (M b))
          ((1 : K) ⊗ₜ[R] (r ⊗ₜ[S] m))) = _
        simp [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have hinj (b : Bool) : Function.Injective (ev b) :=
    tensorImageHom_injective (eR b) Subtype.val_injective
  have hmap (b : Bool) (x : R ⊗[S] M b) : ev (!b) (F b x) = ev b x := by
    rw [hev, hev]
    exact hF b x
  let f : R ⊗[S] M₀ →ₐ[R] R ⊗[S] M₁ := F false
  let g : R ⊗[S] M₁ →ₐ[R] R ⊗[S] M₀ := F true
  have hfg : f.comp g = AlgHom.id R (R ⊗[S] M₁) := by
    apply AlgHom.ext
    intro x
    apply hinj true
    exact (hmap false (g x)).trans (hmap true x)
  have hgf : g.comp f = AlgHom.id R (R ⊗[S] M₀) := by
    apply AlgHom.ext
    intro x
    apply hinj false
    exact (hmap true (f x)).trans (hmap false x)
  let E : R ⊗[S] M₀ ≃ₐ[R] R ⊗[S] M₁ := AlgEquiv.ofAlgHom f g hfg hgf
  refine ⟨R, hR, hSR, E, fun x => ?_⟩
  change e true (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
    (AlgHom.id S (M true)) (f x)) = e false
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S (M false)) x)
  rw [← hev true, ← hev false]
  exact hmap false x

end FrobeniusSplitting
