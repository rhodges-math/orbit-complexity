import OrbitComplexity.FrobeniusSplitting.Normality.Models.RetainedNormalization
import OrbitComplexity.FrobeniusSplitting.Normality.Models.NormalizationProperties
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Normalization over a prescribed affine model

The finite normalization and a principal-open comparison are retained over
one scalar extension of a prescribed finitely presented affine algebra.
The prescribed source and its field comparison are preserved.
-/

set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace FrobeniusSplitting
universe u

open private finite_tensor from
  OrbitComplexity.FrobeniusSplitting.Normality.Models.FiniteNormalizationModels
open private rebased_comparison_square from
  OrbitComplexity.FrobeniusSplitting.Normality.Images.ModelScalarSquares
open private awayModelData retainedAwayData away_transport from
  OrbitComplexity.FrobeniusSplitting.Normality.Models.RetainedNormalization

private def finiteAwayData {S T K M A B : Type u}
    [CommRing S] [CommRing T] [CommRing K] [CommRing M] [CommRing A] [CommRing B]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    [Algebra S M] [Algebra K A] [Algebra K B]
    (eM : K ⊗[S] M ≃ₐ[K] A) (fK : A →ₐ[K] B) : Prop :=
  ∃ N : CommAlgCat.{u} T, Algebra.FinitePresentation T N ∧
    ∃ (f : T ⊗[S] M →ₐ[T] N) (eN : K ⊗[T] N ≃ₐ[K] B),
      f.toRingHom.Finite ∧
      eN.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
        fK.comp ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM).toAlgHom ∧
      ∃ d : T ⊗[S] M,
        modelEval ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM) d ≠ 0 ∧
        IsRegular (modelEval eN (f d)) ∧ awayModelData f d

private theorem finite_away_join {S R T K M N A B : Type u}
    [CommRing S] [CommRing R] [CommRing T] [CommRing K]
    [CommRing M] [CommRing N] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra R T] [Algebra S T] [IsScalarTower S R T]
    [Algebra S K] [Algebra R K] [Algebra T K]
    [IsScalarTower S R K] [IsScalarTower S T K] [IsScalarTower R T K]
    [Algebra S M] [Algebra R N] [Algebra.FinitePresentation R N]
    [Algebra K A] [Algebra K B]
    (eM : K ⊗[S] M ≃ₐ[K] A) (eN : K ⊗[R] N ≃ₐ[K] B)
    (f : R ⊗[S] M →ₐ[R] N) (fK : A →ₐ[K] B) (hf : f.toRingHom.Finite)
    (hmap : eN.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
      fK.comp ((Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM).toAlgHom)
    (d : A) (hd : d ≠ 0) (hregular : IsRegular (fK d))
    (hAway : retainedAwayData (T := T)
      ((Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM) f d) :
    finiteAwayData (T := T) eM fK := by
  let eMR := (Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM
  let eMT := (Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM
  let eOuter := (Algebra.TensorProduct.cancelBaseChange R T K K (R ⊗[S] M)).trans eMR
  let eNT := (Algebra.TensorProduct.cancelBaseChange R T K K N).trans eN
  let fOuter := Algebra.TensorProduct.lTensor (S := T) T f
  let cM := Algebra.TensorProduct.cancelBaseChange S R T T M
  let fT : T ⊗[S] M →ₐ[T] T ⊗[R] N := fOuter.comp cM.symm.toAlgHom
  have hfinite : fT.toRingHom.Finite :=
    (finite_tensor f hf (T := T)).comp cM.symm.toRingEquiv.finite
  have hOuter := rebased_comparison_square (S := R) (R := T) eMR eN f fK hmap
  have hpOuter := points_of_tensor_square eOuter eNT fOuter fK hOuter
  have hp (m : T ⊗[S] M) : modelEval eNT (fT m) = fK (modelEval eMT m) := by
    have hx := DFunLike.congr_fun hpOuter (cM.symm m)
    exact hx.trans (congrArg fK (by
      rw [← modelEval_flatten, cM.apply_symm_apply]))
  have hfinal := tensor_square_of_points eMT eNT fT fK hp
  obtain ⟨dOuter, hden, E, hE⟩ := hAway
  have hcancel : (AlgEquiv.refl : T ⊗[R] N ≃ₐ[T] T ⊗[R] N).toAlgHom.comp fOuter =
      fT.comp cM.toAlgHom := by
    apply AlgHom.ext
    intro x
    change fOuter x = fOuter (cM.symm (cM x))
    rw [cM.symm_apply_apply]
  obtain ⟨ET, hET⟩ := away_transport cM (AlgEquiv.refl : T ⊗[R] N ≃ₐ[T] T ⊗[R] N)
    fOuter fT hcancel dOuter E hE
  have hdenT : modelEval eMT (cM dOuter) = d := (modelEval_flatten eM dOuter).trans hden
  have hvalue : modelEval eNT (fT (cM dOuter)) = fK d :=
    (hp (cM dOuter)).trans (congrArg fK hdenT)
  have hregularT : IsRegular (modelEval eNT (fT (cM dOuter))) := hvalue.symm ▸ hregular
  exact ⟨CommAlgCat.of T (T ⊗[R] N), inferInstance, fT, eNT, hfinite, hfinal,
    cM dOuter, (fun hz => hd (hdenT.symm.trans hz)), hregularT, ET, hET⟩

/-- The finite normalization admits a coefficient model over a scalar
extension of a prescribed affine algebra. Its original field comparison,
nonzero denominator and principal-localization triangle are retained together. -/
theorem exists_normalization_model {K A M : Type u}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A] [CommRing M]
    (S : Subalgebra ℤ K) (hS : S.FG)
    [Algebra S M] [Algebra.FinitePresentation S M] (eM : K ⊗[S] M ≃ₐ[K] A) :
    ∃ (T : Subalgebra ℤ K), T.FG ∧ ∃ hST : S ≤ T,
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
      finiteAwayData (T := T) eM
        (IsScalarTower.toAlgHom K A (integralClosure A (FractionRing A))) := by
  let : Algebra.FinitePresentation K A := Algebra.FinitePresentation.equiv eM
  let : Algebra.FiniteType K A := inferInstance
  let N := integralClosure A (FractionRing A)
  obtain ⟨hfin, _hfp, _hdom, _hic, _hi, d, hd, hregular, E, hE⟩ :=
    normalization_properties (K := K) (A := A)
  let : Module.Finite A N := hfin
  let fK : A →ₐ[K] N := IsScalarTower.toAlgHom K A N
  obtain ⟨R, hR, hSR, B₀, hfpB₀, f, eN, hf, hmap⟩ :=
    exists_finite_model_on (B := N) S hS eM
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let : Algebra.FinitePresentation R B₀ := hfpB₀
  let eMR := (Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM
  obtain ⟨T, hRT, hT, hAway⟩ := exists_retained_away R hR eMR eN f fK hmap d hregular E hE
  let hST : S ≤ T := hSR.trans hRT
  let : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
  have hp := finite_away_join (S := S) (R := R) (T := T) eM eN f fK hf hmap
    d hd hregular hAway
  exact ⟨T, hT, hST, hp⟩

end FrobeniusSplitting
