import OrbitComplexity.FrobeniusSplitting.Normality.Products.ChosenSmoothModels
import OrbitComplexity.FrobeniusSplitting.Normality.FiniteModels

/-! # Smooth coefficient extensions of fixed flat models

An independently smooth model is compared to a specified flat model by identity
maps on the same generic algebra. Coefficient enlargement then preserves the
specified model as a tensor product.
-/

open scoped TensorProduct
namespace FrobeniusSplitting
noncomputable section
universe u

/-- A fixed finitely presented flat model of a smooth algebra becomes smooth
after a finitely generated extension of its coefficient subring. -/
theorem exists_smooth_model_extension {K A : Type u}
    [CommRing K] [CommRing A] [Algebra K A]
    (S : Subalgebra ℤ K) (hS : S.FG) (M : Type u)
    [CommRing M] [Algebra S M] [Algebra.FinitePresentation S M] [Module.Flat S M]
    (e : K ⊗[S] M ≃ₐ[K] A) [Algebra.Smooth K A] :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      R.FG ∧ Algebra.Smooth R (R ⊗[S] M) := by
  obtain ⟨T, N, ringN, algN, hT, hN, eN⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ K A
  let : CommRing N := ringN
  let : Algebra T N := algN
  have : Algebra.Smooth T N := hN
  let U : Subalgebra ℤ K := S ⊔ T
  have hSU : S ≤ U := le_sup_left
  have hTU : T ≤ U := le_sup_right
  let : Algebra S U := (Subalgebra.inclusion hSU).toAlgebra
  let : Algebra T U := (Subalgebra.inclusion hTU).toAlgebra
  have : IsScalarTower S U K := Subalgebra.inclusion.isScalarTower_right hSU K
  have : IsScalarTower T U K := Subalgebra.inclusion.isScalarTower_right hTU K
  let M1 := U ⊗[S] M
  let N1 := U ⊗[T] N
  let eM1 : K ⊗[U] M1 ≃ₐ[K] A :=
    (Algebra.TensorProduct.cancelBaseChange S U K K M).trans e
  let eN1 : K ⊗[U] N1 ≃ₐ[K] A :=
    (Algebra.TensorProduct.cancelBaseChange T U K K N).trans eN.some.symm
  obtain ⟨R, hUR, hR, hsm⟩ :=
    exists_smooth_chosen_basechange U (hS.sup hT) M1 N1 A eM1 eN1
  let : Algebra U R := (Subalgebra.inclusion hUR).toAlgebra
  have : IsScalarTower U R K := Subalgebra.inclusion.isScalarTower_right hUR K
  have hSR : S ≤ R := hSU.trans hUR
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  have : IsScalarTower S U R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  have : Algebra.Smooth R (R ⊗[U] M1) := hsm
  let E : R ⊗[U] M1 ≃ₐ[R] R ⊗[S] M :=
    Algebra.TensorProduct.cancelBaseChange S U R R M
  exact ⟨R, hSR, hR, Algebra.Smooth.of_equiv (R := R) (A := R ⊗[U] M1) E⟩

end
end FrobeniusSplitting
