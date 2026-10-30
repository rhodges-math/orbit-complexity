import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingApplication
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendScalarComparisons
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Polynomial field charts on a common matching cover

The two coefficient extensions and their chart projections determine the
polynomial field charts on the same common affine refinement.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u

open private finalCoefficient oldCoefficient initialCoefficient polynomialSpecMap
  polynomial_spec_comp from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendScalarComparisons
open private inverse_chart_base from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingApplication

private theorem two_chart_projections {C : Type*} [Category C]
    {A B D E F G H : C} (e₁ : A ≅ B) (e₂ : D ≅ E)
    (f₁ : A ⟶ F) (f₂ : D ⟶ G) (q₂ : G ⟶ F) (q₁ : F ⟶ H)
    (k₂ : E ⟶ B) (k₁ : B ⟶ H)
    (h₂ : f₂ ≫ q₂ = e₂.hom ≫ k₂ ≫ e₁.inv ≫ f₁)
    (h₁ : (e₁.inv ≫ f₁) ≫ q₁ = k₁) :
    (e₂.inv ≫ f₂) ≫ (q₂ ≫ q₁) = k₂ ≫ k₁ := by
  have h := inverse_chart_base e₂ f₂ q₂ (k₂ ≫ e₁.inv ≫ f₁) h₂
  calc
    (e₂.inv ≫ f₂) ≫ (q₂ ≫ q₁) = ((e₂.inv ≫ f₂) ≫ q₂) ≫ q₁ :=
      (Category.assoc _ _ _).symm
    _ = (k₂ ≫ e₁.inv ≫ f₁) ≫ q₁ := congrArg (· ≫ q₁) h
    _ = k₂ ≫ ((e₁.inv ≫ f₁) ≫ q₁) := by simp only [Category.assoc]
    _ = k₂ ≫ k₁ := congrArg (k₂ ≫ ·) h₁

private theorem composite_projection {C : Type*} [Category C]
    {A B D E : C} (n : A ⟶ B) (q₂ : B ⟶ D) (q₁ : D ⟶ E)
    (m₁ : A ⟶ D) (m : A ⟶ E)
    (h₂ : n ≫ q₂ = m₁) (h₁ : m₁ ≫ q₁ = m) :
    n ≫ (q₂ ≫ q₁) = m :=
  (Category.assoc n q₂ q₁).symm.trans
    ((congrArg (· ≫ q₁) h₂).trans h₁)

private theorem square_chart_iso {C : Type*} [Category C]
    {A B D E F : C} (e : A ≅ B) (k : D ⟶ B) (j : D ⟶ E)
    (f : A ⟶ F) (n : E ⟶ F)
    (h : IsPullback k j (e.inv ≫ f) n) :
    IsPullback (k ≫ e.inv) j f n := by
  exact h.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

section Charts

variable {S T R K : Type u}
    [CommRing S] [CommRing T] [CommRing R] [CommRing K]
    [Algebra S T] [Algebra T R]
    [Algebra S K] [Algebra T K] [Algebra R K]
    [IsScalarTower S T K] [IsScalarTower T R K]
    {X Y H Z : Scheme.{u}}
    (base : X ⟶ Spec (.of S)) (baseT : Y ⟶ Spec (.of T))
    (baseR : H ⟶ Spec (.of R)) (baseK : Z ⟶ Spec (.of K))
    (q₁ : Y ⟶ X) (q₂ : H ⟶ Y)
    (n : Z ⟶ H) (m₁ : Z ⟶ Y) (m : Z ⟶ X)
    (hK : IsPullback n baseK baseR
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (h₀ : IsPullback m baseK base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hn : n ≫ q₂ = m₁) (hm : m₁ ≫ q₁ = m)
    (U : X.OpenCover.{u})
    (A : U.I₀ → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    (B : U.I₀ → Type u) [∀ j, CommRing (B j)] [∀ j, Algebra K (B j)]
    (e : ∀ j, K ⊗[S] A j ≃ₐ[K] B j)
    (eU : ∀ j, U.X j ≅ Spec (.of (Polynomial (A j))))
    (V₁ : Y.OpenCover.{u}) (index₁ : V₁.I₀ ≃ U.I₀)
    (eV₁ : ∀ j, V₁.X j ≅ Spec (.of (Polynomial (T ⊗[S] A (index₁ j)))))
    (hV₁ : ∀ j, V₁.f j ≫ q₁ = (eV₁ j).hom ≫
      polynomialSpecMap
        (Algebra.TensorProduct.includeRight : A (index₁ j) →ₐ[S]
          T ⊗[S] A (index₁ j)).toRingHom ≫
            (eU (index₁ j)).inv ≫ U.f (index₁ j))
    (V : H.OpenCover.{u}) (index₂ : V.I₀ ≃ V₁.I₀)
    (eV : ∀ j, V.X j ≅
      Spec (.of (Polynomial (R ⊗[T] (T ⊗[S] A (index₁ (index₂ j)))))))
    (hV : ∀ j, V.f j ≫ q₂ = (eV j).hom ≫
      polynomialSpecMap
        (Algebra.TensorProduct.includeRight : T ⊗[S] A (index₁ (index₂ j)) →ₐ[T]
          R ⊗[T] (T ⊗[S] A (index₁ (index₂ j)))).toRingHom ≫
            (eV₁ (index₂ j)).inv ≫ V₁.f (index₂ j))
    (hVbase : ∀ j, V.f j ≫ baseR = (eV j).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Polynomial (R ⊗[T] (T ⊗[S] A (index₁ (index₂ j))))))))
    (jK : ∀ j, Spec (.of (Polynomial (B j))) ⟶ Z)
    (hjK : ∀ j, jK j ≫ m =
      polynomialSpecMap (initialCoefficient (e j)) ≫ (eU j).inv ≫ U.f j)
    (hjKb : ∀ j, jK j ≫ baseK =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial (B j)))))


include base baseR baseK q₁ q₂ m₁ m hK h₀ hn hm eU eV₁ hV₁ hV hVbase hjK hjKb in
private theorem original_polynomial_chart (j : V.I₀) :
    IsPullback
      (polynomialSpecMap (finalCoefficient (T := T) (R := R) (e (index₁ (index₂ j)))) ≫
        (eV j).inv)
      (jK (index₁ (index₂ j))) (V.f j) n := by
  have hmid := inverse_chart_base (eV₁ (index₂ j)) (V₁.f (index₂ j)) q₁
    (polynomialSpecMap
      (Algebra.TensorProduct.includeRight : A (index₁ (index₂ j)) →ₐ[S]
        T ⊗[S] A (index₁ (index₂ j))).toRingHom ≫
          (eU (index₁ (index₂ j))).inv ≫ U.f (index₁ (index₂ j)))
    (hV₁ (index₂ j))
  have htwo := two_chart_projections (eV₁ (index₂ j)) (eV j)
    (V₁.f (index₂ j)) (V.f j) q₂ q₁
    (polynomialSpecMap
      (Algebra.TensorProduct.includeRight : T ⊗[S] A (index₁ (index₂ j)) →ₐ[T]
        R ⊗[T] (T ⊗[S] A (index₁ (index₂ j)))).toRingHom)
    _ (hV j) hmid
  have hold : ((eV j).inv ≫ V.f j) ≫ (q₂ ≫ q₁) =
      polynomialSpecMap (oldCoefficient (S := S) (T := T) (R := R)
        (A := A (index₁ (index₂ j)))) ≫
          ((eU (index₁ (index₂ j))).inv ≫ U.f (index₁ (index₂ j))) := by
    exact htwo.trans (by
      rw [← Category.assoc, polynomial_spec_comp]
      rfl)
  have hbase := inverse_chart_base (eV j) (V.f j) baseR
    (Spec.map (CommRingCat.ofHom
      (algebraMap R (Polynomial (R ⊗[T] (T ⊗[S] A (index₁ (index₂ j))))))))
    (hVbase j)
  have h := iteratedAppend_field_chart (T := T) (R := R)
    (e (index₁ (index₂ j))) (q₂ ≫ q₁) n m base baseR baseK hK h₀
    (composite_projection n q₂ q₁ m₁ m hn hm)
    ((eU (index₁ (index₂ j))).inv ≫ U.f (index₁ (index₂ j)))
    ((eV j).inv ≫ V.f j) (jK (index₁ (index₂ j)))
    hold hbase (hjK (index₁ (index₂ j))) (hjKb (index₁ (index₂ j)))
  exact square_chart_iso (eV j) _ _ (V.f j) n h.1

variable [H.IsSeparated] (W : H.OpenCover.{u})
    [∀ w, IsAffine (W.X w)] [∀ j, IsAffine (V.X j)]

/-- Common affine coordinates with polynomial field charts from the original atlas. -/
def appendMatchingChartSpec
    (_hR : Function.Injective (algebraMap R K)) : Prop :=
  ∃ (hsm : Smooth baseR) (hWfinite : Finite W.I₀) (hVfinite : Finite V.I₀),
    let : Smooth baseR := hsm
    let : Finite W.I₀ := hWfinite
    let : Finite V.I₀ := hVfinite
    ∃ _hchart : ∀ j, IsPullback
        (polynomialSpecMap
          (finalCoefficient (T := T) (R := R) (e (index₁ (index₂ j)))) ≫ (eV j).inv)
        (jK (index₁ (index₂ j))) (V.f j) n,
      type_of% (exists_append_matching_coordinates _hR baseR baseK n hK W V
        (fun j => Spec (.of (Polynomial (B (index₁ (index₂ j))))))
        (fun j => polynomialSpecMap
          (finalCoefficient (T := T) (R := R) (e (index₁ (index₂ j)))) ≫ (eV j).inv)
        (fun j => jK (index₁ (index₂ j))) _hchart)

variable [Smooth baseR] [Finite W.I₀] [Finite V.I₀]

include base q₁ q₂ m₁ m h₀ hn hm eU eV₁ hV₁ hV hVbase hjK hjKb in
/-- Construct field polynomial charts and their common-cover tensor comparisons. -/
theorem append_matching_field_charts (hR : Function.Injective (algebraMap R K)) :
    appendMatchingChartSpec baseR baseK n hK U A B e V₁ index₁ V index₂ eV jK W hR := by
  have hchart := original_polynomial_chart base baseR baseK q₁ q₂ n m₁ m hK h₀ hn hm
    U A B e eU V₁ index₁ eV₁ hV₁ V index₂ eV hV hVbase jK hjK hjKb
  refine ⟨inferInstance, inferInstance, inferInstance, hchart, ?_⟩
  exact exists_append_matching_coordinates hR baseR baseK n hK W V
    (fun j => Spec (.of (Polynomial (B (index₁ (index₂ j))))))
    (fun j => polynomialSpecMap
      (finalCoefficient (T := T) (R := R) (e (index₁ (index₂ j)))) ≫ (eV j).inv)
    (fun j => jK (index₁ (index₂ j))) hchart

end Charts

end SchubertGeometry
