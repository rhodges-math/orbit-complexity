import OrbitComplexity.FrobeniusSplitting.Normality.Models.NormalizationModels
import OrbitComplexity.FrobeniusSplitting.Normality.Models.RegularLocalizationStages
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Normalization models with regular fibre denominators

Finite normalization models and their principal-localization comparisons are
retained at a common coefficient stage. The chosen denominator is regular
after every further coefficient extension.
-/

set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace FrobeniusSplitting
universe u

open private finiteAwayData from
  OrbitComplexity.FrobeniusSplitting.Normality.Models.NormalizationModels
open private finite_tensor from
  OrbitComplexity.FrobeniusSplitting.Normality.Models.FiniteNormalizationModels
open private rebased_comparison_square from
  OrbitComplexity.FrobeniusSplitting.Normality.Images.ModelScalarSquares
open private modelEval_pure_rebase awayModelData away_transport from
  OrbitComplexity.FrobeniusSplitting.Normality.Models.RetainedNormalization

/-- A finite algebra model on a prescribed scalar source retains its field
comparison and principal-localization triangle, with a denominator regular
over every coefficient algebra. The propositions record coefficient bounds. -/
def RegularNormalizationData {S R K M A N : Type u}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A] [CommRing N]
    [Algebra S R] [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    [Algebra S M] [Algebra K A] [Algebra K N]
    (eM : K ⊗[S] M ≃ₐ[K] A) (fK : A →ₐ[K] N) (P Q : Prop) : Prop :=
  ∃ B : CommAlgCat.{u} R, Algebra.FinitePresentation R B ∧
    ∃ (f : R ⊗[S] M →ₐ[R] B) (eB : K ⊗[R] B ≃ₐ[K] N),
      P ∧ Q ∧ f.toRingHom.Finite ∧
      eB.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
        fK.comp ((Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM).toAlgHom ∧
      ∃ d : R ⊗[S] M,
        modelEval ((Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM) d ≠ 0 ∧
        awayModelData f d ∧
        ∀ (L : Type u) [CommRing L] [Algebra R L],
          IsRegular ((1 : L) ⊗ₜ[R] f d : L ⊗[R] B)

private theorem comparison_on_elements {T R K B N : Type u}
    [CommRing T] [CommRing R] [CommRing K] [CommRing B] [CommRing N]
    [Algebra T R] [Algebra T K] [Algebra R K] [IsScalarTower T R K]
    [Algebra T B] [Algebra K N]
    (e : K ⊗[T] B ≃ₐ[K] N) (eR : K ⊗[R] (R ⊗[T] B) ≃ₐ[K] N)
    (h : ∀ b, eR ((1 : K) ⊗ₜ[R] ((1 : R) ⊗ₜ[T] b)) = e ((1 : K) ⊗ₜ[T] b)) :
    eR.toAlgHom = ((Algebra.TensorProduct.cancelBaseChange T R K K B).trans e).toAlgHom := by
  let : Algebra R N := Algebra.compHom N (algebraMap R K)
  let : Algebra T N := Algebra.compHom N (algebraMap T K)
  let : IsScalarTower R K N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower T K N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower T R N := IsScalarTower.of_algebraMap_eq fun t => by
    change algebraMap K N (algebraMap T K t) =
      algebraMap K N (algebraMap R K (algebraMap T R t))
    rw [← IsScalarTower.algebraMap_apply T R K]
  apply Algebra.TensorProduct.ext
  · ext
  · apply Algebra.TensorProduct.ext
    · ext
    · apply AlgHom.ext
      intro b
      change eR ((1 : K) ⊗ₜ[R] ((1 : R) ⊗ₜ[T] b)) =
        e (Algebra.TensorProduct.cancelBaseChange T R K K B
          ((1 : K) ⊗ₜ[R] ((1 : R) ⊗ₜ[T] b)))
      rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
      exact h b

private theorem regular_normalization_packet {S T R K M B A N : Type u}
    [CommRing S] [CommRing T] [CommRing R] [CommRing K]
    [CommRing M] [CommRing B] [CommRing A] [CommRing N]
    [Algebra S T] [Algebra T R] [Algebra S R] [IsScalarTower S T R]
    [Algebra S K] [Algebra T K] [Algebra R K]
    [IsScalarTower S T K] [IsScalarTower S R K] [IsScalarTower T R K]
    [Algebra S M] [Algebra T B] [Algebra.FinitePresentation T B]
    [Algebra K A] [Algebra K N]
    (eM : K ⊗[S] M ≃ₐ[K] A) (eB : K ⊗[T] B ≃ₐ[K] N)
    (f : T ⊗[S] M →ₐ[T] B) (fK : A →ₐ[K] N) (hf : f.toRingHom.Finite)
    (hmap : eB.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
      fK.comp ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM).toAlgHom)
    (d : T ⊗[S] M)
    (hd : modelEval ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM) d ≠ 0)
    (P Q : Prop) (hdata : RegularLocalizationData (R := R) f eB d P Q) :
    RegularNormalizationData (R := R) eM fK P Q := by
  obtain ⟨eR, hP, hQ, _hFree, _hQuot, heR, hAway, hReg⟩ := hdata
  let eMT := (Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM
  let eMR := (Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM
  let eOuter := (Algebra.TensorProduct.cancelBaseChange T R K K (T ⊗[S] M)).trans eMT
  let eBR := (Algebra.TensorProduct.cancelBaseChange T R K K B).trans eB
  let cM := Algebra.TensorProduct.cancelBaseChange S T R R M
  let fOuter := Algebra.TensorProduct.lTensor (S := R) R f
  let fR : R ⊗[S] M →ₐ[R] R ⊗[T] B := fOuter.comp cM.symm.toAlgHom
  have hfinite : fR.toRingHom.Finite :=
    (finite_tensor f hf (T := R)).comp cM.symm.toRingEquiv.finite
  have hCompare := comparison_on_elements eB eR heR
  have hOuter := rebased_comparison_square (S := T) (R := R) eMT eB f fK hmap
  have hField : eR.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K fOuter) =
      fK.comp eOuter.toAlgHom :=
    (congrArg (fun p : K ⊗[R] (R ⊗[T] B) →ₐ[K] N =>
      p.comp (Algebra.TensorProduct.lTensor (S := K) K fOuter)) hCompare).trans hOuter
  have hpOuter := points_of_tensor_square eOuter eR fOuter fK hField
  have hp (m : R ⊗[S] M) : modelEval eR (fR m) = fK (modelEval eMR m) := by
    have hx := DFunLike.congr_fun hpOuter (cM.symm m)
    exact hx.trans (congrArg fK (by
      rw [← modelEval_flatten, cM.apply_symm_apply]))
  have hFinal := tensor_square_of_points eMR eR fR fK hp
  let dOuter : R ⊗[T] (T ⊗[S] M) := (1 : R) ⊗ₜ[T] d
  let dR : R ⊗[S] M := cM dOuter
  have hden : modelEval eMR dR = modelEval eMT d :=
    (modelEval_flatten eM dOuter).trans (modelEval_pure_rebase eMT d)
  have hfd : fR dR = ((1 : R) ⊗ₜ[T] f d) := by
    change fOuter (cM.symm (cM dOuter)) = _
    rw [cM.symm_apply_apply]
    rfl
  have hcancel : (AlgEquiv.refl : R ⊗[T] B ≃ₐ[R] R ⊗[T] B).toAlgHom.comp fOuter =
      fR.comp cM.toAlgHom := by
    apply AlgHom.ext
    intro x
    change fOuter x = fOuter (cM.symm (cM x))
    rw [cM.symm_apply_apply]
  obtain ⟨E, hE⟩ := hAway
  obtain ⟨ER, hER⟩ := away_transport cM (AlgEquiv.refl : R ⊗[T] B ≃ₐ[R] R ⊗[T] B)
    fOuter fR hcancel dOuter E hE
  have hUniversal : ∀ (L : Type u) [CommRing L] [Algebra R L],
      IsRegular ((1 : L) ⊗ₜ[R] fR dR : L ⊗[R] (R ⊗[T] B)) := by
    intro L _ _
    rw [hfd]
    exact hReg L
  exact ⟨CommAlgCat.of R (R ⊗[T] B), inferInstance, fR, eR, hP, hQ, hfinite,
    hFinal, dR, (fun hz => hd (hden.symm.trans hz)), ⟨ER, hER⟩, hUniversal⟩

private theorem exists_after_model {K A N M : Type u}
    [Field K] [CommRing A] [CommRing N] [CommRing M]
    [Algebra K A] [Algebra K N]
    (S T : Subalgebra ℤ K) (hT : T.FG) (hST : S ≤ T)
    [Algebra S M] (eM : K ⊗[S] M ≃ₐ[K] A) (fK : A →ₐ[K] N)
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
    let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
    finiteAwayData (T := T) eM fK →
      ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
        let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
        let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
        RegularNormalizationData (R := R) eM fK R.FG (start ≤ R) := by
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  intro _ _ hdata
  obtain ⟨B, hfpB, f, eB, hf, hmap, d, hd, hregular, E, hE⟩ := hdata
  let : Algebra.FinitePresentation T B := hfpB
  obtain ⟨R, hTR, hRegular⟩ := exists_regular_localization_stage T hT f eB d
    hregular E hE start hstart
  let hSR : S ≤ R := hST.trans hTR
  let : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S T R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let : IsScalarTower T R K := Subalgebra.inclusion.isScalarTower_right hTR K
  have hp := regular_normalization_packet (S := S) (T := T) (R := R) eM eB f fK
    hf hmap d hd R.FG (start ≤ R) hRegular
  exact ⟨R, hSR, hp⟩

/-- A prescribed affine model admits a finite normalization model over one
coefficient extension above a requested starting ring. Its localization
comparison is retained and its denominator is regular over every later algebra. -/
theorem exists_regular_normalization_model {K A M : Type u}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A] [CommRing M]
    (S : Subalgebra ℤ K) (hS : S.FG)
    [Algebra S M] [Algebra.FinitePresentation S M] (eM : K ⊗[S] M ≃ₐ[K] A)
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      RegularNormalizationData (R := R) eM
        (IsScalarTower.toAlgHom K A (integralClosure A (FractionRing A))) R.FG (start ≤ R) := by
  obtain ⟨T, hT, hST, hdata⟩ := exists_normalization_model S hS eM
  exact exists_after_model S T hT hST eM
    (IsScalarTower.toAlgHom K A (integralClosure A (FractionRing A))) start hstart hdata

end FrobeniusSplitting
