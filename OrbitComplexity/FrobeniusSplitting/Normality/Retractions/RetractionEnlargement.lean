import OrbitComplexity.FrobeniusSplitting.Normality.Retractions.PrescribedRetraction

/-! Preservation of the original map's retraction on enlarging coefficients. -/

open scoped TensorProduct

namespace FrobeniusSplitting

variable {S R T M N : Type*}
    [CommRing S] [CommRing R] [CommRing T] [CommRing M] [CommRing N]
    [Algebra S R] [Algebra R T] [Algebra S T] [IsScalarTower S R T]
    [Algebra S M] [Algebra S N]

private theorem cancel_map_square (f : M →ₐ[S] N) (x : T ⊗[R] (R ⊗[S] M)) :
    Algebra.TensorProduct.cancelBaseChange S R T T N
        (Algebra.TensorProduct.lTensor (S := T) T
          (Algebra.TensorProduct.lTensor (S := R) R f) x) =
      Algebra.TensorProduct.lTensor (S := T) T f
        (Algebra.TensorProduct.cancelBaseChange S R T T M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t z =>
    induction z using TensorProduct.inductionOn with
    | tmul r m => rfl
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Enlarging coefficients preserves a retraction of the prescribed tensor map. -/
theorem retraction_enlarge (f : M →ₐ[S] N)
    (r : R ⊗[S] N →ₗ[R] R ⊗[S] M)
    (hr : r.comp (Algebra.TensorProduct.lTensor (S := R) R f).toLinearMap =
      LinearMap.id) :
    ∃ q : T ⊗[S] N →ₗ[T] T ⊗[S] M,
      q.comp (Algebra.TensorProduct.lTensor (S := T) T f).toLinearMap =
        LinearMap.id := by
  let cM : T ⊗[R] (R ⊗[S] M) ≃ₐ[T] T ⊗[S] M :=
    Algebra.TensorProduct.cancelBaseChange S R T T M
  let cN : T ⊗[R] (R ⊗[S] N) ≃ₐ[T] T ⊗[S] N :=
    Algebra.TensorProduct.cancelBaseChange S R T T N
  let g := Algebra.TensorProduct.lTensor (S := T) T
    (Algebra.TensorProduct.lTensor (S := R) R f)
  let rT := r.baseChange T
  have hrT : rT.comp g.toLinearMap = LinearMap.id := by
    change (r.baseChange T).comp
      ((Algebra.TensorProduct.lTensor (S := R) R f).toLinearMap.baseChange T) =
        LinearMap.id
    rw [← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
  refine ⟨cM.toLinearMap.comp (rT.comp cN.symm.toLinearMap), ?_⟩
  apply LinearMap.ext
  intro x
  change cM (rT (cN.symm (Algebra.TensorProduct.lTensor (S := T) T f x))) = x
  have hs : cN (g (cM.symm x)) = Algebra.TensorProduct.lTensor (S := T) T f x :=
    (cancel_map_square f (cM.symm x)).trans
      (congrArg (Algebra.TensorProduct.lTensor (S := T) T f) (cM.apply_symm_apply x))
  have heq : cN.symm (Algebra.TensorProduct.lTensor (S := T) T f x) = g (cM.symm x) :=
    cN.injective ((cN.apply_symm_apply _).trans hs.symm)
  rw [heq]
  have h := LinearMap.congr_fun hrT (cM.symm x)
  change rT (g (cM.symm x)) = cM.symm x at h
  rw [h, cM.apply_symm_apply]

end FrobeniusSplitting
