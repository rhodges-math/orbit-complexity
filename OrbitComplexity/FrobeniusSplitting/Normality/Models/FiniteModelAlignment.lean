import OrbitComplexity.FrobeniusSplitting.Normality.Retractions.ModelIsoFamily
import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.FreeBaseChange
import Mathlib.RingTheory.Flat.Basic

/-! # Simultaneous alignment of specified finite algebra models

The node isomorphisms retain their original generic evaluations. Making the
second node family free first ensures that equality of those evaluations
also proves every original arrow square on one coefficient enlargement.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

noncomputable section

universe u v w

private theorem free_model_family {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {I : Type v} [Finite I]
    (M : I → Type u) [∀ i, CommRing (M i)] [∀ i, Algebra S (M i)]
    [∀ i, Algebra.FinitePresentation S (M i)] :
    ∃ (T : Subalgebra ℤ K), T.FG ∧ ∃ hST : S ≤ T,
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      ∀ i, Module.Free T (T ⊗[S] M i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  choose T hT hST hfree using fun i ↦ exists_free_baseChange (B := M i) S hS
  have hfg (s : Finset I) : (s.sup T).FG := by
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.sup_empty] using
          (Subalgebra.fg_bot : (⊥ : Subalgebra ℤ K).FG)
    | @insert i s _ ih =>
        simpa only [Finset.sup_insert] using (hT i).sup ih
  let R : Subalgebra ℤ K := S ⊔ Finset.univ.sup T
  have hR : R.FG := hS.sup (hfg Finset.univ)
  have hSR : S ≤ R := le_sup_left
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  refine ⟨R, hR, hSR, fun i ↦ ?_⟩
  have hTR : T i ≤ R :=
    (show T i ≤ Finset.univ.sup T from Finset.le_sup (Finset.mem_univ i)).trans
      le_sup_right
  let : Algebra S (T i) := (Subalgebra.inclusion (hST i)).toAlgebra
  let : Algebra (T i) R := (Subalgebra.inclusion hTR).toAlgebra
  let : IsScalarTower S (T i) R := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Module.Free (T i) (T i ⊗[S] M i) := hfree i
  exact Module.Free.of_equiv
    (Algebra.TensorProduct.cancelBaseChange S (T i) R R (M i)).toLinearEquiv

private def evaluateModel {S R K M A : Type u}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] [Algebra K A]
    (e : K ⊗[S] M ≃ₐ[K] A) (x : R ⊗[S] M) : A :=
  e (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M) x)

private theorem evaluateModel_map {S R K A B A' B' : Type u}
    [CommRing S] [CommRing R] [CommRing K]
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S A] [Algebra S B] [Algebra K A'] [Algebra K B']
    (eA : K ⊗[S] A ≃ₐ[K] A') (eB : K ⊗[S] B ≃ₐ[K] B')
    (f : A →ₐ[S] B) (g : A' →ₐ[K] B')
    (h : eB.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
      g.comp eA.toAlgHom) (x : R ⊗[S] A) :
    evaluateModel eB (Algebra.TensorProduct.lTensor (S := R) R f x) =
      g (evaluateModel eA x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
      exact AlgHom.congr_fun h ((algebraMap R K r) ⊗ₜ[S] a)
  | add x y hx hy =>
      simpa only [evaluateModel, map_add] using congrArg₂ (· + ·) hx hy

private theorem evaluateModel_cancel {S T R K M A : Type u}
    [CommRing S] [CommRing T] [CommRing R] [CommRing K]
    [CommRing M] [CommRing A]
    [Algebra S T] [Algebra S R] [Algebra T R] [IsScalarTower S T R]
    [Algebra S K] [Algebra T K] [Algebra R K]
    [IsScalarTower S T K] [IsScalarTower S R K] [IsScalarTower T R K]
    [Algebra S M] [Algebra K A]
    (e : K ⊗[S] M ≃ₐ[K] A) (x : R ⊗[T] (T ⊗[S] M)) :
    evaluateModel e (Algebra.TensorProduct.cancelBaseChange S T R R M x) =
      evaluateModel ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans e) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
      induction x using TensorProduct.inductionOn with
      | tmul t m =>
          simp only [evaluateModel, AlgEquiv.trans_apply,
            Algebra.TensorProduct.cancelBaseChange_tmul,
            Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
          change e ((algebraMap R K (t • r)) ⊗ₜ[S] m) =
            e ((t • algebraMap R K r) ⊗ₜ[S] m)
          apply congrArg (fun k : K ↦ e (k ⊗ₜ[S] m))
          simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply T R K]
      | add x y hx hy =>
          simpa only [evaluateModel, TensorProduct.tmul_add, map_add] using
            congrArg₂ (· + ·) hx hy
  | add x y hx hy =>
      simpa only [evaluateModel, map_add] using congrArg₂ (· + ·) hx hy

private theorem evaluateModel_injective {S R K M A : Type u}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] [Algebra K A] [Module.Flat S M]
    (e : K ⊗[S] M ≃ₐ[K] A)
    (hi : Function.Injective (algebraMap R K)) :
    Function.Injective (evaluateModel (R := R) e) := by
  let eR : K ⊗[R] (R ⊗[S] M) ≃ₐ[K] A :=
    (Algebra.TensorProduct.cancelBaseChange S R K K M).trans e
  have he (x : R ⊗[S] M) :
      eR ((1 : K) ⊗ₜ[R] x) = evaluateModel e x := by
    induction x using TensorProduct.inductionOn with
    | tmul r m =>
        simp only [eR, evaluateModel, AlgEquiv.trans_apply,
          Algebra.TensorProduct.cancelBaseChange_tmul,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        congr 2
        simp [Algebra.smul_def]
    | add x y hx hy =>
        simpa only [evaluateModel, TensorProduct.tmul_add, map_add] using
          congrArg₂ (· + ·) hx hy
  have hright : Function.Injective
      (Algebra.TensorProduct.includeRight :
        R ⊗[S] M →ₐ[R] K ⊗[R] (R ⊗[S] M)) :=
    Algebra.TensorProduct.includeRight_injective hi
  intro x y hxy
  apply hright
  apply eR.injective
  change eR ((1 : K) ⊗ₜ[R] x) = eR ((1 : K) ⊗ₜ[R] y)
  rw [he, he]
  exact hxy

private theorem conjugate_evaluation {A₀ A₁ B₀ B₁ C : Type*}
    (c₀ : A₀ ≃ B₀) (c₁ : A₁ ≃ B₁) (E : A₀ ≃ A₁)
    (p₀ : B₀ → C) (p₁ : B₁ → C) (q₀ : A₀ → C) (q₁ : A₁ → C)
    (h₀ : ∀ z, p₀ (c₀ z) = q₀ z) (h₁ : ∀ z, p₁ (c₁ z) = q₁ z)
    (hE : ∀ z, q₁ (E z) = q₀ z) (x : B₀) :
    p₁ (c₁ (E (c₀.symm x))) = p₀ x := by
  rw [h₁, hE, ← h₀, c₀.apply_symm_apply]

private theorem injective_of_equiv_evaluation {A B C : Type*}
    (c : A ≃ B) (p : B → C) (q : A → C)
    (h : ∀ z, p (c z) = q z) (hq : Function.Injective q) :
    Function.Injective p := by
  intro x y hxy
  apply c.symm.injective
  apply hq
  rw [← h, ← h, c.apply_symm_apply, c.apply_symm_apply]
  exact hxy

private theorem model_alignment_from_free
    {S T R K : Type u} [CommRing S] [CommRing T] [CommRing R] [Field K]
    [Algebra S T] [Algebra T R] [Algebra S R]
    [Algebra S K] [Algebra T K] [Algebra R K]
    [IsScalarTower S T R] [IsScalarTower S T K]
    [IsScalarTower S R K] [IsScalarTower T R K]
    {I : Type v} {J : Type w}
    (M₀ M₁ A : I → Type u)
    [∀ i, CommRing (M₀ i)] [∀ i, CommRing (M₁ i)] [∀ i, CommRing (A i)]
    [∀ i, Algebra S (M₀ i)] [∀ i, Algebra S (M₁ i)] [∀ i, Algebra K (A i)]
    [∀ i, Module.Free T (T ⊗[S] M₁ i)]
    (e₀ : ∀ i, K ⊗[S] M₀ i ≃ₐ[K] A i)
    (e₁ : ∀ i, K ⊗[S] M₁ i ≃ₐ[K] A i)
    (src tgt : J → I)
    (f₀ : ∀ j, M₀ (src j) →ₐ[S] M₀ (tgt j))
    (f₁ : ∀ j, M₁ (src j) →ₐ[S] M₁ (tgt j))
    (a : ∀ j, A (src j) →ₐ[K] A (tgt j))
    (h₀ : ∀ j, (e₀ (tgt j)).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (f₀ j)) =
        (a j).comp (e₀ (src j)).toAlgHom)
    (h₁ : ∀ j, (e₁ (tgt j)).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (f₁ j)) =
        (a j).comp (e₁ (src j)).toAlgHom)
    (E : ∀ i, R ⊗[T] (T ⊗[S] M₀ i) ≃ₐ[R] R ⊗[T] (T ⊗[S] M₁ i))
    (hE : ∀ i x,
      evaluateModel (R := R)
        ((Algebra.TensorProduct.cancelBaseChange S T K K (M₁ i)).trans (e₁ i))
        (E i x) =
      evaluateModel (R := R)
        ((Algebra.TensorProduct.cancelBaseChange S T K K (M₀ i)).trans (e₀ i)) x)
    (hRK : Function.Injective (algebraMap R K)) :
    ∃ F : ∀ i, R ⊗[S] M₀ i ≃ₐ[R] R ⊗[S] M₁ i,
      (∀ i x, evaluateModel (R := R) (e₁ i) (F i x) =
        evaluateModel (R := R) (e₀ i) x) ∧
      ∀ j, (F (tgt j)).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := R) R (f₀ j)) =
        (Algebra.TensorProduct.lTensor (S := R) R (f₁ j)).comp
          (F (src j)).toAlgHom := by
  let e₀T (i) : K ⊗[T] (T ⊗[S] M₀ i) ≃ₐ[K] A i :=
    (Algebra.TensorProduct.cancelBaseChange S T K K (M₀ i)).trans (e₀ i)
  let e₁T (i) : K ⊗[T] (T ⊗[S] M₁ i) ≃ₐ[K] A i :=
    (Algebra.TensorProduct.cancelBaseChange S T K K (M₁ i)).trans (e₁ i)
  let c₀ (i) : R ⊗[T] (T ⊗[S] M₀ i) ≃ₐ[R] R ⊗[S] M₀ i :=
    Algebra.TensorProduct.cancelBaseChange S T R R (M₀ i)
  let c₁ (i) : R ⊗[T] (T ⊗[S] M₁ i) ≃ₐ[R] R ⊗[S] M₁ i :=
    Algebra.TensorProduct.cancelBaseChange S T R R (M₁ i)
  let F (i) : R ⊗[S] M₀ i ≃ₐ[R] R ⊗[S] M₁ i :=
    (c₀ i).symm.trans ((E i).trans (c₁ i))
  have hF (i : I) (x : R ⊗[S] M₀ i) :
      evaluateModel (e₁ i) (F i x) = evaluateModel (e₀ i) x := by
    change evaluateModel (e₁ i) (c₁ i (E i ((c₀ i).symm x))) =
      evaluateModel (e₀ i) x
    exact conjugate_evaluation (c₀ i).toEquiv (c₁ i).toEquiv (E i).toEquiv
      (evaluateModel (R := R) (e₀ i)) (evaluateModel (R := R) (e₁ i))
      (evaluateModel (R := R) (e₀T i)) (evaluateModel (R := R) (e₁T i))
      (fun z => evaluateModel_cancel (S := S) (T := T) (R := R)
        (K := K) (M := M₀ i) (A := A i) (e₀ i) z)
      (fun z => evaluateModel_cancel (S := S) (T := T) (R := R)
        (K := K) (M := M₁ i) (A := A i) (e₁ i) z)
      (hE i) x
  have hinj (i : I) : Function.Injective (evaluateModel (R := R) (e₁ i)) := by
    exact injective_of_equiv_evaluation (c₁ i).toEquiv
      (evaluateModel (R := R) (e₁ i)) (evaluateModel (R := R) (e₁T i))
      (fun z => evaluateModel_cancel (S := S) (T := T) (R := R)
        (K := K) (M := M₁ i) (A := A i) (e₁ i) z)
      (evaluateModel_injective (S := T) (R := R) (K := K)
        (M := T ⊗[S] M₁ i) (A := A i) (e₁T i) hRK)
  refine ⟨F, hF, fun j ↦ ?_⟩
  apply AlgHom.ext
  intro x
  apply hinj (tgt j)
  exact (hF (tgt j) _).trans
    ((evaluateModel_map (e₀ (src j)) (e₀ (tgt j)) (f₀ j) (a j) (h₀ j) x).trans
      ((congrArg (a j) (hF (src j) x).symm).trans
        (evaluateModel_map (e₁ (src j)) (e₁ (tgt j)) (f₁ j) (a j) (h₁ j)
          (F (src j) x)).symm))

end
end FrobeniusSplitting
