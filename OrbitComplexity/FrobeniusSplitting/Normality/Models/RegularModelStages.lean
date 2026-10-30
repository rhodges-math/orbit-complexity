import OrbitComplexity.FrobeniusSplitting.Normality.Models.RegularFibres
import OrbitComplexity.FrobeniusSplitting.Normality.Models.FiniteModelAlignment
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coefficient stages with regular fibre denominators

A finitely presented algebra and the quotient by a regular denominator become
free over a common coefficient ring. Projectivity of the quotient then
preserves regularity over every further coefficient algebra.
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

open private free_model_family
  from OrbitComplexity.FrobeniusSplitting.Normality.Models.FiniteModelAlignment

private theorem free_later (S T R B : Type u)
    [CommRing S] [CommRing T] [CommRing R] [CommRing B]
    [Algebra S T] [Algebra S R] [Algebra T R] [IsScalarTower S T R]
    [Algebra S B] [Module.Free T (T ⊗[S] B)] :
    Module.Free R (R ⊗[S] B) := by
  let E : R ⊗[T] (T ⊗[S] B) ≃ₐ[R] R ⊗[S] B :=
    Algebra.TensorProduct.cancelBaseChange S T R R B
  exact Module.Free.of_equiv E.toLinearEquiv

private def principalTensorIso {S R B : Type u}
    [CommRing S] [CommRing R] [CommRing B] [Algebra S R] [Algebra S B]
    (d : B) :
    R ⊗[S] (B ⧸ Ideal.span ({d} : Set B)) ≃ₐ[R]
      (R ⊗[S] B) ⧸ Ideal.span ({(1 : R) ⊗ₜ[S] d} : Set (R ⊗[S] B)) := by
  let I : Ideal B := Ideal.span ({d} : Set B)
  have hI : I.map (Algebra.TensorProduct.includeRight :
        B →ₐ[S] R ⊗[S] B).toRingHom =
      Ideal.span ({(1 : R) ⊗ₜ[S] d} : Set (R ⊗[S] B)) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  exact (Algebra.TensorProduct.tensorQuotientEquiv R B R I).trans
    (Ideal.quotientEquivAlgOfEq R hI)

private theorem fibre_regular_of_field_comparison
    {R K M N : Type u} [CommRing R] [CommRing K]
    [CommRing M] [CommRing N] [Algebra R K] [Algebra R M]
    [Algebra K N] [Module.Free R M]
    (e : K ⊗[R] M ≃ₐ[K] N)
    (hi : Function.Injective (algebraMap R K)) (d : M)
    [Module.Free R (M ⧸ Ideal.span ({d} : Set M))]
    (hd : IsRegular (e ((1 : K) ⊗ₜ[R] d))) :
    ∀ (L : Type u) [CommRing L] [Algebra R L],
      IsRegular ((1 : L) ⊗ₜ[R] d : L ⊗[R] M) := by
  let : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 hi
  let f : M →+* N := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : M →ₐ[R] K ⊗[R] M).toRingHom
  have hι : Function.Injective
      (Algebra.TensorProduct.includeRight : M →ₐ[R] K ⊗[R] M) :=
    Module.Flat.tensorProduct_mk_injective (R := R) (M := M) (S := K)
  have hf : Function.Injective f := e.injective.comp hι
  have hd' : IsRegular (f d) := hd
  have hM : IsRegular d := by
    constructor
    · intro x y h
      apply hf
      apply hd'.left
      simpa only [map_mul] using congrArg f h
    · intro x y h
      apply hf
      apply hd'.right
      simpa only [map_mul] using congrArg f h
  intro L _ _
  exact regular_tmul_of_projective_quotient d hM L

private theorem regular_stage_compare
    {S R K B N : Type u} [CommRing S] [CommRing R] [CommRing K]
    [CommRing B] [CommRing N] [Algebra S R] [Algebra S K]
    [Algebra R K] [IsScalarTower S R K] [Algebra S B] [Algebra K N]
    (e : K ⊗[S] B ≃ₐ[K] N)
    (hi : Function.Injective (algebraMap R K)) (d : B)
    (hd : IsRegular (e ((1 : K) ⊗ₜ[S] d)))
    (hfree : Module.Free R (R ⊗[S] B))
    (hquot : Module.Free R (R ⊗[S] (B ⧸ Ideal.span ({d} : Set B)))) :
    ∃ eR : K ⊗[R] (R ⊗[S] B) ≃ₐ[K] N,
      Module.Free R ((R ⊗[S] B) ⧸
        Ideal.span ({(1 : R) ⊗ₜ[S] d} : Set (R ⊗[S] B))) ∧
      (∀ b : B, eR ((1 : K) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] b)) = e ((1 : K) ⊗ₜ[S] b)) ∧
      ∀ (L : Type u) [CommRing L] [Algebra R L],
        IsRegular ((1 : L) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] d) : L ⊗[R] (R ⊗[S] B)) := by
  let : Module.Free R (R ⊗[S] B) := hfree
  let : Module.Free R (R ⊗[S] (B ⧸ Ideal.span ({d} : Set B))) := hquot
  let dR : R ⊗[S] B := (1 : R) ⊗ₜ[S] d
  let EQ : R ⊗[S] (B ⧸ Ideal.span ({d} : Set B)) ≃ₐ[R]
      (R ⊗[S] B) ⧸ Ideal.span ({dR} : Set (R ⊗[S] B)) :=
    principalTensorIso (S := S) (R := R) d
  let : Module.Free R ((R ⊗[S] B) ⧸ Ideal.span ({dR} : Set (R ⊗[S] B))) :=
    Module.Free.of_equiv EQ.toLinearEquiv
  let eR : K ⊗[R] (R ⊗[S] B) ≃ₐ[K] N :=
    (Algebra.TensorProduct.cancelBaseChange S R K K B).trans e
  have heR (b : B) :
      eR ((1 : K) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] b)) = e ((1 : K) ⊗ₜ[S] b) := by
    simp [eR]
  have hn : IsRegular (eR ((1 : K) ⊗ₜ[R] dR)) := (heR d).symm ▸ hd
  have hregular := fibre_regular_of_field_comparison
    (R := R) (K := K) (M := R ⊗[S] B) (N := N) eR hi dR hn
  exact ⟨eR, inferInstance, heR, hregular⟩

/-- An algebra and a principal quotient become free at one coefficient
extension, where a regular generic denominator remains regular over every
further coefficient algebra. The field comparison retains the old elements. -/
theorem exists_regular_model_stage
    {K B N : Type u} [Field K] [CommRing B] [CommRing N] [Algebra K N]
    (S : Subalgebra ℤ K) (hS : S.FG) [Algebra S B]
    [Algebra.FinitePresentation S B]
    (e : K ⊗[S] B ≃ₐ[K] N) (d : B)
    (hd : IsRegular (e ((1 : K) ⊗ₜ[S] d)))
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      ∃ eR : K ⊗[R] (R ⊗[S] B) ≃ₐ[K] N,
        R.FG ∧ start ≤ R ∧ Module.Free R (R ⊗[S] B) ∧
        Module.Free R ((R ⊗[S] B) ⧸
          Ideal.span ({(1 : R) ⊗ₜ[S] d} : Set (R ⊗[S] B))) ∧
        (∀ b : B, eR ((1 : K) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] b)) = e ((1 : K) ⊗ₜ[S] b)) ∧
        ∀ (L : Type u) [CommRing L] [Algebra R L],
          IsRegular ((1 : L) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] d) : L ⊗[R] (R ⊗[S] B)) := by
  let I : Ideal B := Ideal.span ({d} : Set B)
  let : Algebra.FinitePresentation S (B ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton d)
  let M : Bool → Type u := fun b => if b then B else B ⧸ I
  let (b : Bool) : CommRing (M b) := by cases b <;> dsimp [M] <;> infer_instance
  let (b : Bool) : Algebra S (M b) := by cases b <;> dsimp [M] <;> infer_instance
  let (b : Bool) : Algebra.FinitePresentation S (M b) := by
    cases b <;> dsimp [M] <;> infer_instance
  obtain ⟨T, hT, hST, hFree⟩ := free_model_family S hS M
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let R := T ⊔ start
  have hTR : T ≤ R := le_sup_left
  have hSR : S ≤ R := hST.trans hTR
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
  let : IsScalarTower S T R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let : Module.Free T (T ⊗[S] B) := by
    change Module.Free T (T ⊗[S] M true)
    exact hFree true
  let : Module.Free T (T ⊗[S] (B ⧸ I)) := by
    change Module.Free T (T ⊗[S] M false)
    exact hFree false
  have hfree : Module.Free R (R ⊗[S] B) := free_later S T R B
  have hquot : Module.Free R (R ⊗[S] (B ⧸ I)) := free_later S T R (B ⧸ I)
  obtain ⟨eR, hfreeQuot, heR, hregular⟩ := regular_stage_compare
    (S := S) (R := R) (K := K) (B := B) (N := N) e
    (show Function.Injective (algebraMap R K) from Subtype.val_injective) d hd hfree hquot
  exact ⟨R, hSR, eR, hT.sup hstart, le_sup_right, hfree, hfreeQuot, heR, hregular⟩

end FrobeniusSplitting
