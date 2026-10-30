import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendAtlas
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingCover
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Polynomial chart comparison after a coefficient extension

Tensor cancellation preserves the coefficient map from the preceding ring.
The two structure maps then determine the polynomial chart over the extended
model, with the prescribed field chart as its scalar extension.
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open FrobeniusSplitting

namespace SchubertGeometry

open private tensor_coordinate_factor from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendAtlas

section Coefficients

variable {S T K A B : Type u}
  [CommRing S] [CommRing T] [CommRing K] [CommRing A] [CommRing B]
  [Algebra S T] [Algebra T K] [Algebra S K] [IsScalarTower S T K]
  [Algebra S A] [Algebra K B]

private abbrev extendedEquiv (e : K ⊗[S] A ≃ₐ[K] B) :
    K ⊗[T] (T ⊗[S] A) ≃ₐ[K] B :=
  (Algebra.TensorProduct.cancelBaseChange S T K K A).trans e

private abbrev extendedCoefficient (e : K ⊗[S] A ≃ₐ[K] B) :
    T ⊗[S] A →+* B :=
  (extendedEquiv (T := T) e).toRingHom.comp
    Algebra.TensorProduct.includeRight.toRingHom

/-- Tensor cancellation preserves the whole polynomial coefficient map. -/
theorem scalarPolynomial_composition (e : K ⊗[S] A ≃ₐ[K] B) :
    Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (extendedCoefficient (T := T) e))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom)) =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))) := by
  have hp := (Polynomial.mapRingHom_comp (extendedCoefficient (T := T) e)
    (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom).trans
      (congrArg Polynomial.mapRingHom (tensor_coordinate_factor (R := T) e))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hp

/-- The specified field polynomial chart is Cartesian over the extended
model once its two projections agree with those of the preceding model. -/
theorem scalarPolynomial_field_chart (e : K ⊗[S] A ≃ₐ[K] B)
    {X Y Z : Scheme.{u}} (q : Y ⟶ X) (n : Z ⟶ Y) (m : Z ⟶ X)
    (base : X ⟶ Spec (.of S)) (baseT : Y ⟶ Spec (.of T))
    (baseK : Z ⟶ Spec (.of K))
    (hK : IsPullback n baseK baseT
      (Spec.map (CommRingCat.ofHom (algebraMap T K))))
    (h₀ : IsPullback m baseK base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hm : n ≫ q = m)
    (j₀ : Spec (.of (Polynomial A)) ⟶ X)
    (jT : Spec (.of (Polynomial (T ⊗[S] A))) ⟶ Y)
    (jK : Spec (.of (Polynomial B)) ⟶ Z)
    (hjT : jT ≫ q = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom)) ≫ j₀)
    (hjTb : jT ≫ baseT =
      Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial (T ⊗[S] A)))))
    (hjK : jK ≫ m = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))) ≫ j₀)
    (hjKb : jK ≫ baseK =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial B)))) :
    IsPullback
        (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (extendedCoefficient (T := T) e)))) jK jT n ∧
      jK ≫ n = Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (extendedCoefficient (T := T) e))) ≫ jT := by
  obtain ⟨_, _, _, hP⟩ := exists_scalar_polynomial_square T K (T ⊗[S] A) B
    (extendedEquiv (T := T) e)
  exact append_scalar_field_chart q n m base baseT baseK _ _ hK h₀ hm
    _ _ _ (scalarPolynomial_composition (T := T) e) _ _ hP
    j₀ jT jK hjT hjTb hjK hjKb

end Coefficients

end SchubertGeometry
