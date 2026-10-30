import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Models.FiniteRelations
import Mathlib.RingTheory.Extension.Generators
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Surjectivity at a finite coefficient stage

A finite family of algebra maps with finite type targets, surjective after
extension to a field, becomes surjective over one finitely generated
coefficient ring containing any prescribed finitely generated subalgebra.
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FrobeniusSplitting

universe u v

private def tensor_right_map {S : Type*} [CommRing S]
    (R : Type*) [CommRing R] [Algebra S R]
    {A B : Type*} [CommRing A] [CommRing B] [Algebra S A] [Algebra S B]
    (f : A →ₐ[S] B) : R ⊗[S] A →ₐ[R] R ⊗[S] B :=
  Algebra.TensorProduct.map (AlgHom.id R R) f

private theorem surjective_of_generator_lifts
    {S A B I : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] (P : Algebra.Generators S B I)
    (f : A →ₐ[S] B) (w : I → A) (hw : ∀ i, f (w i) = P.val i) :
    Function.Surjective f := by
  have he : f.comp (MvPolynomial.aeval w) = MvPolynomial.aeval P.val := by
    ext i
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hw i
  intro b
  obtain ⟨p, hp⟩ := P.aeval_val_surjective b
  refine ⟨MvPolynomial.aeval w p, ?_⟩
  exact (congrArg (fun g : MvPolynomial I S →ₐ[S] B => g p) he).trans hp

private theorem tensor_cokernel_exact
    {S A B : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] (R : Type*) [CommRing R] [Algebra S R]
    (f : A →ₐ[S] B) :
    Function.Exact (f.toLinearMap.lTensor R)
      (f.toLinearMap.range.mkQ.lTensor R) :=
  lTensor_exact R (LinearMap.exact_iff.mpr
    (Submodule.ker_mkQ (p := f.toLinearMap.range)))
    (Submodule.mkQ_surjective _)

private theorem tensor_cokernel_zero
    {S A B : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] (K : Type*) [CommRing K] [Algebra S K]
    (f : A →ₐ[S] B) (hf : Function.Surjective (tensor_right_map K f)) (b : B) :
    (1 : K) ⊗ₜ[S] f.toLinearMap.range.mkQ b = 0 := by
  have h := (tensor_cokernel_exact K f ((1 : K) ⊗ₜ[S] b)).mpr
    (hf ((1 : K) ⊗ₜ[S] b))
  exact h

private theorem surjective_of_cokernel_zero
    {S A B I : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] (R : Type*) [CommRing R] [Algebra S R]
    (P : Algebra.Generators S B I) (f : A →ₐ[S] B)
    (hz : ∀ i, (1 : R) ⊗ₜ[S] f.toLinearMap.range.mkQ (P.val i) = 0) :
    Function.Surjective (tensor_right_map R f) := by
  classical
  have hlift (i : I) : ∃ w : R ⊗[S] A,
      tensor_right_map R f w = (1 : R) ⊗ₜ[S] P.val i :=
    (tensor_cokernel_exact R f ((1 : R) ⊗ₜ[S] P.val i)).mp (hz i)
  choose w hw using hlift
  exact surjective_of_generator_lifts (P.baseChange R) (tensor_right_map R f) w hw

private theorem zero_relations_of_le
    {K : Type u} [Field K] (S T R : Subalgebra ℤ K)
    (hST : S ≤ T) (hTR : T ≤ R)
    {I : Type v} (M : I → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module S (M i)]
    (x : ∀ i, M i) :
    let _ : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
    let _ : Algebra S R := (Subalgebra.inclusion (hST.trans hTR)).toAlgebra
    (∀ i, (1 : T) ⊗ₜ[S] x i = 0) → ∀ i, (1 : R) ⊗ₜ[S] x i = 0 := by
  intro _ _ hz i
  let t : T →ₗ[S] R :=
    { toFun := fun a => ⟨a.val, hTR a.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact congrArg (TensorProduct.map t (LinearMap.id : M i →ₗ[S] M i)) (hz i)

/-- A finite family of algebra maps with finite type targets, surjective over a
field, is surjective over one finitely generated coefficient extension containing
a prescribed finitely generated subalgebra. -/
theorem exists_surjective_family_stage
    {K : Type u} [Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} [Finite I] (A B : I → Type u)
    [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra S (A i)] [∀ i, Algebra S (B i)]
    [∀ i, Algebra.FiniteType S (B i)]
    (f : ∀ i, A i →ₐ[S] B i)
    (hf : ∀ i, Function.Surjective
      (Algebra.TensorProduct.map (AlgHom.id K K) (f i)))
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let _ : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let _ : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      R.FG ∧ start ≤ R ∧ ∀ i, Function.Surjective
        (Algebra.TensorProduct.map (AlgHom.id R R) (f i)) := by
  classical
  choose n hP using fun i =>
    (Algebra.FiniteType.iff_exists_generators (R := S) (S := B i)).mp inferInstance
  let P (i : I) : Algebra.Generators S (B i) (Fin (n i)) := Classical.choice (hP i)
  let J := Σ i : I, Fin (n i)
  let Q (j : J) := B j.1 ⧸ (f j.1).toLinearMap.range
  let x (j : J) : Q j := (f j.1).toLinearMap.range.mkQ ((P j.1).val j.2)
  have hx (j : J) : (1 : K) ⊗ₜ[S] x j = 0 :=
    tensor_cokernel_zero K (f j.1) (hf j.1) ((P j.1).val j.2)
  obtain ⟨T, hST, hT, hzero⟩ := exists_retained_zero_relations S hS Q x hx
  let R : Subalgebra ℤ K := T ⊔ start
  have hTR : T ≤ R := le_sup_left
  have hSR : S ≤ R := hST.trans hTR
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  have hz : ∀ j, (1 : R) ⊗ₜ[S] x j = 0 :=
    zero_relations_of_le S T R hST hTR Q x hzero
  exact ⟨R, hSR, hT.sup hstart, le_sup_right, fun i =>
    surjective_of_cokernel_zero R (P i) (f i) (fun k => hz ⟨i, k⟩)⟩

end FrobeniusSplitting
