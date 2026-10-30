import OrbitComplexity.FrobeniusSplitting.Normality.Retractions.MixedIsoFamily
import Mathlib.RingTheory.TensorProduct.Free

/-! Retractions for prescribed maps after enlarging the coefficient ring. -/

open scoped TensorProduct

universe u

namespace FrobeniusSplitting

private theorem generic_map_square {S R K M N : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing N]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] [Algebra S N] (f : M →ₐ[S] N) (x : R ⊗[S] M) :
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S N)
        (Algebra.TensorProduct.lTensor (S := R) R f x) =
      Algebra.TensorProduct.lTensor (S := K) K f
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem generic_cancel {S R K M : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] (x : R ⊗[S] M) :
    Algebra.TensorProduct.cancelBaseChange S R K K M
        ((Algebra.TensorProduct.includeRight : R ⊗[S] M →ₐ[R]
          K ⊗[R] (R ⊗[S] M)) x) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r m =>
    change Algebra.TensorProduct.cancelBaseChange S R K K M (1 ⊗ₜ[R] (r ⊗ₜ[S] m)) =
      (algebraMap R K r) ⊗ₜ[S] m
    rw [Algebra.TensorProduct.cancelBaseChange_tmul]
    rw [Algebra.smul_def, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A split free image model yields a retraction for the original coefficient map. -/
theorem exists_prescribed_retraction {K : Type u} [Field K]
    (S T : Subalgebra ℤ K) (hT : T.FG) (hST : S ≤ T)
    {M N P Q : Type u} [CommRing M] [CommRing N] [CommRing P] [CommRing Q]
    [Algebra S M] [Algebra S N] [Algebra T P] [Algebra T Q]
    [Algebra.FinitePresentation S M] [Algebra.FinitePresentation S N]
    [Algebra.FinitePresentation T P] [Algebra.FinitePresentation T Q]
    [Module.Free T Q] (f : M →ₐ[S] N) (g : P →ₐ[T] Q)
    (eM : K ⊗[T] P ≃ₐ[K] K ⊗[S] M) (eN : K ⊗[T] Q ≃ₐ[K] K ⊗[S] N)
    (r : Q →ₗ[T] P) (hr : r.comp g.toLinearMap = LinearMap.id)
    (hsq : ∀ y, eN (Algebra.TensorProduct.lTensor (S := K) K g y) =
      Algebra.TensorProduct.lTensor (S := K) K f (eM y)) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ ∃ hTR : T ≤ R,
      letI : Algebra S R := (Subalgebra.inclusion (hST.trans hTR)).toAlgebra
      ∃ r₀ : R ⊗[S] N →ₗ[R] R ⊗[S] M,
        r₀.comp (Algebra.TensorProduct.lTensor (S := R) R f).toLinearMap =
          LinearMap.id := by
  let O : Bool → Type u := fun b => if b then N else M
  let C : Bool → Type u := fun b => if b then Q else P
  let : ∀ b, CommRing (O b) := fun b => by cases b <;> dsimp [O] <;> infer_instance
  let : ∀ b, CommRing (C b) := fun b => by cases b <;> dsimp [C] <;> infer_instance
  let : ∀ b, Algebra S (O b) := fun b => by cases b <;> dsimp [O] <;> infer_instance
  let : ∀ b, Algebra T (C b) := fun b => by cases b <;> dsimp [C] <;> infer_instance
  let : ∀ b, Algebra.FinitePresentation S (O b) := fun b => by
    cases b <;> dsimp [O] <;> infer_instance
  let : ∀ b, Algebra.FinitePresentation T (C b) := fun b => by
    cases b <;> dsimp [C] <;> infer_instance
  let eC (b : Bool) : K ⊗[T] C b ≃ₐ[K] K ⊗[S] O b := by
    cases b
    · exact eM
    · exact eN
  obtain ⟨R, hR, hTR, hE⟩ := exists_mixed_iso_family S T hT hST O C
    (fun b => K ⊗[S] O b) (fun _ => AlgEquiv.refl) eC
  let : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
  let : Algebra S R := (Subalgebra.inclusion (hST.trans hTR)).toAlgebra
  let : IsScalarTower T R K := Subalgebra.inclusion.isScalarTower_right hTR K
  let : IsScalarTower S R K :=
    Subalgebra.inclusion.isScalarTower_right (hST.trans hTR) K
  obtain ⟨EP, hEP⟩ := hE false
  obtain ⟨EQ, hEQ⟩ := hE true
  change R ⊗[S] M ≃ₐ[R] R ⊗[T] P at EP
  change R ⊗[S] N ≃ₐ[R] R ⊗[T] Q at EQ
  change ∀ x, eM (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
    (AlgHom.id T P) (EP x)) = Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom S R K) (AlgHom.id S M) x at hEP
  change ∀ x, eN (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
    (AlgHom.id T Q) (EQ x)) = Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom S R K) (AlgHom.id S N) x at hEQ
  have hrR : (r.baseChange R).comp
      (Algebra.TensorProduct.lTensor (S := R) R g).toLinearMap = LinearMap.id := by
    change (r.baseChange R).comp (g.toLinearMap.baseChange R) = LinearMap.id
    rw [← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
  refine ⟨R, hR, hTR, ?_⟩
  apply retraction_of_generic_square (K := K) Subtype.val_injective
    (Algebra.TensorProduct.lTensor (S := R) R f)
    (Algebra.TensorProduct.lTensor (S := R) R g) EP EQ (r.baseChange R) hrR
  intro x
  apply eN.injective.comp
    (Algebra.TensorProduct.cancelBaseChange T R K K Q).injective
  dsimp only [Function.comp_apply]
  rw [generic_cancel, generic_cancel]
  calc
    eN (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K) (AlgHom.id T Q)
        (EQ (Algebra.TensorProduct.lTensor (S := R) R f x))) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S N)
        (Algebra.TensorProduct.lTensor (S := R) R f x) := hEQ _
    _ = Algebra.TensorProduct.lTensor (S := K) K f
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M) x) :=
      generic_map_square f x
    _ = Algebra.TensorProduct.lTensor (S := K) K f
        (eM (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K) (AlgHom.id T P)
          (EP x))) := congrArg _ (hEP x).symm
    _ = eN (Algebra.TensorProduct.lTensor (S := K) K g
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K) (AlgHom.id T P)
          (EP x))) := (hsq _).symm
    _ = eN (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K) (AlgHom.id T Q)
        (Algebra.TensorProduct.lTensor (S := R) R g (EP x))) :=
      congrArg eN (generic_map_square g (EP x)).symm

end FrobeniusSplitting
