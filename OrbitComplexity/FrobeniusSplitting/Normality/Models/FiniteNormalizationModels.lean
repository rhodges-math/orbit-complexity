import OrbitComplexity.FrobeniusSplitting.Normality.FiniteModelMaps
import OrbitComplexity.FrobeniusSplitting.Normality.Retractions.MixedIsoFamily
import OrbitComplexity.FrobeniusSplitting.Normality.Images.ModelScalarSquares
import Mathlib.RingTheory.TensorProduct.Finite
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Finite algebra models on a prescribed source

An arithmetic model of a finite algebra map can be compared with a prescribed
model of its source. The comparison retains the original map after extending
the coefficient ring.
-/

set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace FrobeniusSplitting
universe u

open private image_cancel_smul
  from OrbitComplexity.FrobeniusSplitting.Normality.Retractions.ModelIsoFamily
open private rebased_comparison_square
  from OrbitComplexity.FrobeniusSplitting.Normality.Images.ModelScalarSquares

private theorem cancel_eval_tmul {S T K M A : Type u}
    [CommRing S] [CommRing T] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    [Algebra S M] [Algebra K A] (e : K ⊗[S] M ≃ₐ[K] A)
    (k : K) (x : T ⊗[S] M) :
    e (Algebra.TensorProduct.cancelBaseChange S T K K M (k ⊗ₜ[T] x)) =
      k • e (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K)
        (AlgHom.id S M) x) := by
  have hid : IsScalarTower.toAlgHom S K K = AlgHom.id S K := by ext; rfl
  have h := image_cancel_smul (S := S) (T := T) (R := K) (K := K) e k x
  simpa only [hid, Algebra.TensorProduct.map_id, AlgHom.id_apply,
    Algebra.algebraMap_self, RingHom.id_apply] using h

private theorem comparison_square {S U T K M N A : Type u}
    [CommRing S] [CommRing U] [CommRing T] [CommRing K]
    [CommRing M] [CommRing N] [CommRing A]
    [Algebra S T] [Algebra U T] [Algebra S K] [Algebra U K] [Algebra T K]
    [IsScalarTower S T K] [IsScalarTower U T K]
    [Algebra S M] [Algebra U N] [Algebra K A]
    (eM : K ⊗[S] M ≃ₐ[K] A) (eN : K ⊗[U] N ≃ₐ[K] A)
    (E : T ⊗[S] M ≃ₐ[T] T ⊗[U] N)
    (hE : ∀ x,
      eN (Algebra.TensorProduct.map (IsScalarTower.toAlgHom U T K) (AlgHom.id U N) (E x)) =
        eM (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K) (AlgHom.id S M) x)) :
    ((Algebra.TensorProduct.cancelBaseChange U T K K N).trans eN).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K E.toAlgHom) =
      ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM).toAlgHom := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul k x =>
      change eN (Algebra.TensorProduct.cancelBaseChange U T K K N (k ⊗ₜ[T] E x)) =
        eM (Algebra.TensorProduct.cancelBaseChange S T K K M (k ⊗ₜ[T] x))
      rw [cancel_eval_tmul eN, cancel_eval_tmul eM, hE]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private theorem finite_tensor {R A B T : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T]
    (f : A →ₐ[R] B) (hf : f.toRingHom.Finite) :
    (Algebra.TensorProduct.lTensor (S := T) T f).toRingHom.Finite := by
  exact RingHom.Finite.tensorProductMap
    (f := AlgHom.id R T) (RingHom.Finite.id T) (g := f) hf

private theorem compose_square {R K M N P A B : Type u}
    [CommRing R] [CommRing K] [CommRing M] [CommRing N] [CommRing P]
    [CommRing A] [CommRing B] [Algebra R K]
    [Algebra R M] [Algebra R N] [Algebra R P] [Algebra K A] [Algebra K B]
    (eM : K ⊗[R] M →ₐ[K] A) (eN : K ⊗[R] N →ₐ[K] A)
    (eP : K ⊗[R] P →ₐ[K] B) (f : N →ₐ[R] P) (g : A →ₐ[K] B)
    (E : M →ₐ[R] N)
    (hf : eP.comp (Algebra.TensorProduct.lTensor (S := K) K f) = g.comp eN)
    (hE : eN.comp (Algebra.TensorProduct.lTensor (S := K) K E) = eM) :
    eP.comp (Algebra.TensorProduct.lTensor (S := K) K (f.comp E)) = g.comp eM := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul k x =>
      change eP (k ⊗ₜ[R] f (E x)) = g (eM (k ⊗ₜ[R] x))
      exact (DFunLike.congr_fun hf (k ⊗ₜ[R] E x)).trans
        (congrArg g (DFunLike.congr_fun hE (k ⊗ₜ[R] x)))
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private theorem finite_model_transport {S U T K M N P A B : Type u}
    [CommRing S] [CommRing U] [CommRing T] [CommRing K]
    [CommRing M] [CommRing N] [CommRing P] [CommRing A] [CommRing B]
    [Algebra S T] [Algebra U T] [Algebra S K] [Algebra U K] [Algebra T K]
    [IsScalarTower S T K] [IsScalarTower U T K]
    [Algebra S M] [Algebra U N] [Algebra U P]
    [Algebra.FinitePresentation U P] [Algebra K A] [Algebra K B]
    (eM : K ⊗[S] M ≃ₐ[K] A) (eN : K ⊗[U] N ≃ₐ[K] A)
    (eP : K ⊗[U] P ≃ₐ[K] B) (fU : N →ₐ[U] P) (gK : A →ₐ[K] B)
    (hfU : fU.toRingHom.Finite)
    (hUmap : eP.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K fU) =
      gK.comp eN.toAlgHom)
    (E : T ⊗[S] M ≃ₐ[T] T ⊗[U] N)
    (hE : ∀ x,
      eN (Algebra.TensorProduct.map (IsScalarTower.toAlgHom U T K) (AlgHom.id U N) (E x)) =
        eM (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K) (AlgHom.id S M) x)) :
    ∃ B₀ : CommAlgCat.{u} T, Algebra.FinitePresentation T B₀ ∧
      ∃ (f : T ⊗[S] M →ₐ[T] B₀) (eB : K ⊗[T] B₀ ≃ₐ[K] B),
        f.toRingHom.Finite ∧
        eB.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
          gK.comp ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM).toAlgHom := by
  let P₀ := T ⊗[U] P
  let g : T ⊗[U] N →ₐ[T] P₀ := Algebra.TensorProduct.lTensor (S := T) T fU
  let f : T ⊗[S] M →ₐ[T] P₀ := g.comp E.toAlgHom
  let eB : K ⊗[T] P₀ ≃ₐ[K] B :=
    (Algebra.TensorProduct.cancelBaseChange U T K K P).trans eP
  have hg : g.toRingHom.Finite := finite_tensor fU hfU (T := T)
  have hf : f.toRingHom.Finite := hg.comp E.toRingEquiv.finite
  have hEmap := comparison_square eM eN E hE
  have hgmap := rebased_comparison_square (S := U) (R := T) eN eP fU gK hUmap
  have hmap := compose_square
    ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM).toAlgHom
    ((Algebra.TensorProduct.cancelBaseChange U T K K N).trans eN).toAlgHom
    eB.toAlgHom g gK E.toAlgHom hgmap hEmap
  exact ⟨CommAlgCat.of T P₀, inferInstance, f, eB, hf, hmap⟩

private theorem exists_aligned_model {K A B M N P : Type u}
    [Field K] [CommRing A] [CommRing B] [CommRing M] [CommRing N] [CommRing P]
    [Algebra K A] [Algebra K B]
    (S U : Subalgebra ℤ K) (hU : U.FG) (hSU : S ≤ U)
    [Algebra S M] [Algebra.FinitePresentation S M]
    [Algebra U N] [Algebra.FinitePresentation U N]
    [Algebra U P] [Algebra.FinitePresentation U P]
    (eM : K ⊗[S] M ≃ₐ[K] A) (eN : K ⊗[U] N ≃ₐ[K] A)
    (eP : K ⊗[U] P ≃ₐ[K] B) (fU : N →ₐ[U] P) (gK : A →ₐ[K] B)
    (hfU : fU.toRingHom.Finite)
    (hUmap : eP.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K fU) =
      gK.comp eN.toAlgHom) :
    ∃ T : Subalgebra ℤ K, T.FG ∧ ∃ hST : S ≤ T,
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
      ∃ B₀ : CommAlgCat.{u} T, Algebra.FinitePresentation T B₀ ∧
        ∃ (f : T ⊗[S] M →ₐ[T] B₀) (eB : K ⊗[T] B₀ ≃ₐ[K] B),
          f.toRingHom.Finite ∧
          eB.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
            gK.comp ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM).toAlgHom := by
  obtain ⟨T, hT, hUT, hIso⟩ := exists_mixed_iso_family S U hU hSU
    (fun _ : Unit => M) (fun _ : Unit => N) (fun _ : Unit => A)
    (fun _ => eM) (fun _ => eN)
  let hST : S ≤ T := hSU.trans hUT
  let : Algebra U T := (Subalgebra.inclusion hUT).toAlgebra
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower U T K := Subalgebra.inclusion.isScalarTower_right hUT K
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  obtain ⟨E, hE⟩ := hIso ()
  have hpacket := finite_model_transport (S := S) (U := U) (T := T)
    (K := K) (M := M) (N := N) (P := P) eM eN eP fU gK hfU hUmap E hE
  exact ⟨T, hT, hST, hpacket⟩

private theorem exists_enlarged_model {K A B M A₁ B₁ : Type u}
    [Field K] [CommRing A] [CommRing B] [CommRing M] [CommRing A₁] [CommRing B₁]
    [Algebra K A] [Algebra K B]
    (S R : Subalgebra ℤ K) (hS : S.FG) (hR : R.FG)
    [Algebra S M] [Algebra.FinitePresentation S M]
    [Algebra R A₁] [Algebra.FinitePresentation R A₁]
    [Algebra R B₁] [Algebra.FinitePresentation R B₁]
    (eA : K ⊗[S] M ≃ₐ[K] A) (eA₁ : K ⊗[R] A₁ ≃ₐ[K] A)
    (eB₁ : K ⊗[R] B₁ ≃ₐ[K] B) (f₁ : A₁ →ₐ[R] B₁) (gK : A →ₐ[K] B)
    (hf₁ : f₁.toRingHom.Finite)
    (hsquare : eB₁.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f₁) =
      gK.comp eA₁.toAlgHom) :
    ∃ T : Subalgebra ℤ K, T.FG ∧ ∃ hST : S ≤ T,
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
      ∃ B₀ : CommAlgCat.{u} T, Algebra.FinitePresentation T B₀ ∧
        ∃ (f : T ⊗[S] M →ₐ[T] B₀) (eB : K ⊗[T] B₀ ≃ₐ[K] B),
          f.toRingHom.Finite ∧
          eB.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
            gK.comp ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans eA).toAlgHom := by
  let U : Subalgebra ℤ K := S ⊔ R
  have hU : U.FG := hS.sup hR
  have hSU : S ≤ U := le_sup_left
  have hRU : R ≤ U := le_sup_right
  let : Algebra S U := (Subalgebra.inclusion hSU).toAlgebra
  let : Algebra R U := (Subalgebra.inclusion hRU).toAlgebra
  let : IsScalarTower S U K := Subalgebra.inclusion.isScalarTower_right hSU K
  let : IsScalarTower R U K := Subalgebra.inclusion.isScalarTower_right hRU K
  let N := U ⊗[R] A₁
  let P := U ⊗[R] B₁
  let eN : K ⊗[U] N ≃ₐ[K] A :=
    (Algebra.TensorProduct.cancelBaseChange R U K K A₁).trans eA₁
  let eP : K ⊗[U] P ≃ₐ[K] B :=
    (Algebra.TensorProduct.cancelBaseChange R U K K B₁).trans eB₁
  let fU : N →ₐ[U] P := Algebra.TensorProduct.lTensor (S := U) U f₁
  have hfU := finite_tensor f₁ hf₁ (T := U)
  have hUmap := rebased_comparison_square (S := R) (R := U) eA₁ eB₁ f₁ gK hsquare
  exact exists_aligned_model S U hU hSU eA eN eP fU gK hfU hUmap

/-- A finite algebra over the generic fibre of a prescribed finitely presented
model has a finite arithmetic model over a scalar extension of that same model.
The algebra map retains its original generic-fibre comparison square. -/
theorem exists_finite_model_on {K A B A₀ : Type u}
    [Field K] [CommRing A] [CommRing B] [CommRing A₀]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    [Module.Finite A B] (S : Subalgebra ℤ K) (hS : S.FG)
    [Algebra S A₀] [Algebra.FinitePresentation S A₀]
    (eA : K ⊗[S] A₀ ≃ₐ[K] A) :
    ∃ T : Subalgebra ℤ K, T.FG ∧ ∃ hST : S ≤ T,
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
      ∃ B₀ : CommAlgCat.{u} T, Algebra.FinitePresentation T B₀ ∧
        ∃ (f : T ⊗[S] A₀ →ₐ[T] B₀) (eB : K ⊗[T] B₀ ≃ₐ[K] B),
          f.toRingHom.Finite ∧
          eB.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
            (IsScalarTower.toAlgHom K A B).comp
              ((Algebra.TensorProduct.cancelBaseChange S T K K A₀).trans eA).toAlgHom := by
  let : Algebra.FinitePresentation K A := Algebra.FinitePresentation.equiv eA
  let : Algebra.FiniteType K B := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K A) (inferInstance : Algebra.FiniteType A B)
  let : Algebra.FinitePresentation K B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨R, A₁, B₁, hAB, hRAB, eA₁, eB₁, hR, hfpA₁, hfpB₁, hfin, _ha, _hb, hsquare⟩ :=
    exists_finite_arithmetic_model (K := K) (A := A) (B := B)
  let : Algebra A₁ B₁ := hAB
  let : IsScalarTower R A₁ B₁ := hRAB
  let : Algebra.FinitePresentation R A₁ := hfpA₁
  let : Algebra.FinitePresentation R B₁ := hfpB₁
  let : Module.Finite A₁ B₁ := hfin
  let f₁ : A₁ →ₐ[R] B₁ := IsScalarTower.toAlgHom R A₁ B₁
  have hf₁ : f₁.toRingHom.Finite := RingHom.finite_algebraMap.mpr hfin
  exact exists_enlarged_model S R hS hR eA eA₁ eB₁ f₁
    (IsScalarTower.toAlgHom K A B) hf₁ hsquare

/-- The algebra-map evaluation determined by a tensor-product isomorphism. -/
def modelEval {R K M A : Type u}
    [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra R K] [Algebra R M] [Algebra K A]
    (e : K ⊗[R] M ≃ₐ[K] A) : M →+* A :=
  e.toRingHom.comp (Algebra.TensorProduct.includeRight : M →ₐ[R] K ⊗[R] M).toRingHom

/-- Evaluation of a flat tensor model is injective along an injective coefficient map. -/
theorem modelEval_injective {R K M A : Type u}
    [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra R K] [Algebra R M] [Algebra K A] [Module.Flat R M]
    (e : K ⊗[R] M ≃ₐ[K] A) (hi : Function.Injective (algebraMap R K)) :
    Function.Injective (modelEval e) :=
  e.injective.comp (Algebra.TensorProduct.includeRight_injective hi)

/-- Evaluation of a scalar-extended tensor model is the tensor-map evaluation. -/
theorem modelEval_rebase {S R K M A : Type u}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    [Algebra S M] [Algebra K A] (e : K ⊗[S] M ≃ₐ[K] A)
    (x : R ⊗[S] M) :
    modelEval ((Algebra.TensorProduct.cancelBaseChange S R K K M).trans e) x =
      e (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M) x) := by
  exact (cancel_eval_tmul e 1 x).trans (one_smul K _)

/-- Equality on model evaluations gives a commutative tensor-product square. -/
theorem tensor_square_of_points {R K M N A B : Type u}
    [CommRing R] [CommRing K] [CommRing M] [CommRing N] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R M] [Algebra R N] [Algebra K A] [Algebra K B]
    (eM : K ⊗[R] M ≃ₐ[K] A) (eN : K ⊗[R] N ≃ₐ[K] B)
    (f : M →ₐ[R] N) (g : A →ₐ[K] B)
    (h : ∀ m, modelEval eN (f m) = g (modelEval eM m)) :
    eN.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
      g.comp eM.toAlgHom := by
  let : Algebra R B := Algebra.compHom B (algebraMap R K)
  let : IsScalarTower R K B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply Algebra.TensorProduct.ext
  · ext
  · exact AlgHom.ext h

/-- A commutative tensor-product square gives equality of model evaluations. -/
theorem points_of_tensor_square {R K M N A B : Type u}
    [CommRing R] [CommRing K] [CommRing M] [CommRing N] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R M] [Algebra R N] [Algebra K A] [Algebra K B]
    (eM : K ⊗[R] M ≃ₐ[K] A) (eN : K ⊗[R] N ≃ₐ[K] B)
    (f : M →ₐ[R] N) (g : A →ₐ[K] B)
    (h : eN.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
      g.comp eM.toAlgHom) :
    (modelEval eN).comp f.toRingHom = g.toRingHom.comp (modelEval eM) := by
  apply RingHom.ext
  intro m
  exact DFunLike.congr_fun h ((1 : K) ⊗ₜ[R] m)

/-- Model evaluation commutes with two successive scalar extensions. -/
theorem modelEval_flatten {S R T K M A : Type u}
    [CommRing S] [CommRing R] [CommRing T] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra R T] [Algebra S T] [IsScalarTower S R T]
    [Algebra S K] [Algebra R K] [Algebra T K]
    [IsScalarTower S R K] [IsScalarTower S T K] [IsScalarTower R T K]
    [Algebra S M] [Algebra K A] (e : K ⊗[S] M ≃ₐ[K] A)
    (x : T ⊗[R] (R ⊗[S] M)) :
    modelEval ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans e)
        (Algebra.TensorProduct.cancelBaseChange S R T T M x) =
      modelEval ((Algebra.TensorProduct.cancelBaseChange R T K K (R ⊗[S] M)).trans
        ((Algebra.TensorProduct.cancelBaseChange S R K K M).trans e)) x := by
  induction x using TensorProduct.inductionOn with
  | tmul t x =>
      rw [modelEval_rebase, modelEval_rebase]
      change e (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K)
          (AlgHom.id S M) (Algebra.TensorProduct.cancelBaseChange S R T T M (t ⊗ₜ[R] x))) =
        e (Algebra.TensorProduct.cancelBaseChange S R K K M
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R T K)
            (AlgHom.id R (R ⊗[S] M)) (t ⊗ₜ[R] x)))
      rw [image_cancel_smul e t x, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        cancel_eval_tmul e]
      rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Tensor cancellation flattens a scalar-extended map and preserves its field equation. -/
theorem flatten_retained_map {S R T K M N A B : Type u}
    [CommRing S] [CommRing R] [CommRing T] [CommRing K]
    [CommRing M] [CommRing N] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra R T] [Algebra S T] [IsScalarTower S R T]
    [Algebra S K] [Algebra R K] [Algebra T K]
    [IsScalarTower S R K] [IsScalarTower S T K] [IsScalarTower R T K]
    [Algebra S M] [Algebra S N] [Algebra K A] [Algebra K B]
    (eM : K ⊗[S] M ≃ₐ[K] A) (eN : K ⊗[S] N ≃ₐ[K] B)
    (qR : R ⊗[S] M →ₐ[R] R ⊗[S] N) (qK : A →ₐ[K] B)
    (hqR : ∀ m,
      eN (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
        (AlgHom.id S N) (qR m)) =
      qK (eM (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
        (AlgHom.id S M) m))) :
    ∃ qT : T ⊗[S] M →ₐ[T] T ⊗[S] N,
      (modelEval ((Algebra.TensorProduct.cancelBaseChange S T K K N).trans eN)).comp
          qT.toRingHom =
        qK.toRingHom.comp
          (modelEval ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM)) := by
  let eMR := (Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM
  let eNR := (Algebra.TensorProduct.cancelBaseChange S R K K N).trans eN
  have hR : eNR.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K qR) =
      qK.comp eMR.toAlgHom := tensor_square_of_points eMR eNR qR qK
        (fun m => by rw [modelEval_rebase, modelEval_rebase]; exact hqR m)
  have hT := rebased_comparison_square (S := R) (R := T) eMR eNR qR qK hR
  let qOuter := Algebra.TensorProduct.lTensor (S := T) T qR
  let cM := Algebra.TensorProduct.cancelBaseChange S R T T M
  let cN := Algebra.TensorProduct.cancelBaseChange S R T T N
  let qT := cN.toAlgHom.comp (qOuter.comp cM.symm.toAlgHom)
  refine ⟨qT, RingHom.ext fun m => ?_⟩
  have hp := DFunLike.congr_fun (points_of_tensor_square
    ((Algebra.TensorProduct.cancelBaseChange R T K K (R ⊗[S] M)).trans eMR)
    ((Algebra.TensorProduct.cancelBaseChange R T K K (R ⊗[S] N)).trans eNR)
    qOuter qK hT) (cM.symm m)
  change modelEval ((Algebra.TensorProduct.cancelBaseChange S T K K N).trans eN)
      (cN (qOuter (cM.symm m))) =
    qK (modelEval ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM) m)
  rw [modelEval_flatten]
  exact hp.trans (congrArg qK (by
    rw [← modelEval_flatten, cM.apply_symm_apply]))

/-- Injective coefficient maps reflect a map triangle and the injectivity of its third map. -/
theorem map_equations_of_injections
    {A B C A' B' C' : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [CommRing A'] [CommRing B'] [CommRing C']
    (a : A →+* A') (b : B →+* B') (c : C →+* C')
    (f : A →+* B) (l : A →+* C) (q : B →+* C)
    (f' : A' →+* B') (l' : A' →+* C') (q' : B' →+* C')
    (hb : Function.Injective b) (hc : Function.Injective c)
    (hq' : Function.Injective q')
    (hf : b.comp f = f'.comp a) (hl : c.comp l = l'.comp a)
    (hq : c.comp q = q'.comp b) (hfl : q'.comp f' = l') :
    Function.Injective q ∧ q.comp f = l := by
  constructor
  · intro x y h
    apply hb
    apply hq'
    have hx := DFunLike.congr_fun hq x
    have hy := DFunLike.congr_fun hq y
    exact hx.symm.trans ((congrArg c h).trans hy)
  · apply RingHom.ext
    intro x
    apply hc
    change c (q (f x)) = c (l x)
    have hqx := DFunLike.congr_fun hq (f x)
    have hfx := DFunLike.congr_fun hf x
    have hlx := DFunLike.congr_fun hl x
    have hflx := DFunLike.congr_fun hfl (a x)
    exact hqx.trans ((congrArg q' hfx).trans (hflx.trans hlx.symm))

end FrobeniusSplitting
