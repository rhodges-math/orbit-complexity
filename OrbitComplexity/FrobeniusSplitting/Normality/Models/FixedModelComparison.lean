import OrbitComplexity.FrobeniusSplitting.Normality.Models.ModelTransitionLifts

/-! # coordinates of the coefficient extension of a chosen diagram -/

open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v w
namespace FrobeniusSplitting

/-- The canonical tensor cancellation preserves every arrow and the evaluation
map of the chosen coordinate diagram after a coefficient enlargement. -/
theorem fixed_model_comparison {C : Type v} [Category.{w} C]
    {S R K : Type u} [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    (M : C ⥤ CommAlgCat.{u} S) (F : C ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
      (F.map f).hom.comp (e s).toAlgHom) :
    let N := fixedFibreDiagram (R := R) (M := R) M
    let d := fun s ↦ (Algebra.TensorProduct.cancelBaseChange S R K K (M.obj s)).trans (e s)
    (∀ s t (f : s ⟶ t), (d t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
      (F.map f).hom.comp (d s).toAlgHom) ∧
    ∀ s (x : N.obj s), d s ((1 : K) ⊗ₜ[R] x) = e s
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
        (AlgHom.id S (M.obj s)) x) := by
  let N := fixedFibreDiagram (R := R) (M := R) M
  let d := fun s ↦ (Algebra.TensorProduct.cancelBaseChange S R K K (M.obj s)).trans (e s)
  have hval (s : C) (x : N.obj s) : d s ((1 : K) ⊗ₜ[R] x) = e s
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
        (AlgHom.id S (M.obj s)) x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
        change e s (Algebra.TensorProduct.cancelBaseChange S R K K (M.obj s)
          ((1 : K) ⊗ₜ[R] (r ⊗ₜ[S] x))) = e s (algebraMap R K r ⊗ₜ[S] x)
        rw [Algebra.TensorProduct.cancelBaseChange_tmul]
        congr 1
        simp only [Algebra.smul_def, mul_one]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  refine ⟨fun s t f ↦ ?_, hval⟩
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul k z =>
      induction z using TensorProduct.inductionOn with
      | tmul r x =>
          change e t (Algebra.TensorProduct.cancelBaseChange S R K K (M.obj t)
              (k ⊗ₜ[R] (r ⊗ₜ[S] (M.map f).hom x))) =
            (F.map f).hom (e s (Algebra.TensorProduct.cancelBaseChange S R K K (M.obj s)
              (k ⊗ₜ[R] (r ⊗ₜ[S] x))))
          rw [Algebra.TensorProduct.cancelBaseChange_tmul,
            Algebra.TensorProduct.cancelBaseChange_tmul]
          exact AlgHom.congr_fun (he s t f) ((r • k) ⊗ₜ[S] x)
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end FrobeniusSplitting
