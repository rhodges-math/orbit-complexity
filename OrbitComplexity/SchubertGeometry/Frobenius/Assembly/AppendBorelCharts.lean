import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingCharts
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Borel polynomial charts on a retained matching model

The polynomial charts of a Borel append atlas determine the field-chart maps
on the common matching cover through both prescribed coefficient extensions.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open FrobeniusSplitting ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct

namespace SchubertGeometry

universe u

open private initialCoefficient polynomialSpecMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendScalarComparisons
open private polynomial_chart_structure from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingStageGeometry

private theorem iso_source_square {C : Type*} [Category C]
    {A B D E F : C} (i : A ≅ B) (f : B ⟶ D)
    (s : B ⟶ E) (t : A ⟶ E) (g : D ⟶ F) (k : E ⟶ F)
    (hs : i.hom ≫ s = t) (h : IsPullback f s g k) :
    IsPullback (i.hom ≫ f) t g k := by
  exact h.of_iso i.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by rw [← hs]; simp) (by simp) (by simp)

private theorem iso_chart_projection {C : Type*} [Category C]
    {A B D E : C} (i : A ≅ B) (j : D ⟶ B) (f : B ⟶ E)
    (k : D ⟶ E) (h : j ≫ f = k) :
    (j ≫ i.inv) ≫ (i.hom ≫ f) = k := by
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

private theorem iso_chart_base {C : Type*} [Category C]
    {A B D E : C} (i : A ≅ B) (j : D ⟶ B) (s : B ⟶ E)
    (t : A ⟶ E) (k : D ⟶ E)
    (hi : i.hom ≫ s = t) (hj : j ≫ s = k) :
    (j ≫ i.inv) ≫ t = k := by
  rw [← hi]
  exact iso_chart_projection i j s k hj

private theorem iso_chart_word {C : Type*} [Category C]
    {A B D : C} (i : A ≅ B) (j : D ⟶ B)
    (r : A ⟶ B) (hr : i.hom = r) :
    (j ≫ i.inv) ≫ r = j := by
  rw [← hr]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem iso_prior_projection {C : Type*} [Category C]
    {A B D E : C} (i : A ≅ B) (m₁ : B ⟶ D)
    (q : D ⟶ E) (m : B ⟶ E) (h : m₁ ≫ q = m) :
    (i.hom ≫ m₁) ≫ q = i.hom ≫ m :=
  (Category.assoc _ _ _).trans (congrArg (i.hom ≫ ·) h)

section BorelCharts

variable {K S T R I : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    [CommRing S] [CommRing T] [CommRing R]
    [Algebra S T] [Algebra T R]
    [Algebra S K] [Algebra T K] [Algebra R K]
    [IsScalarTower S T K] [IsScalarTower T R K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (e : ∀ s, K ⊗[S] N.obj s ≃ₐ[K] F.obj s)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j // j ∈ s.val})
    (V₀ : I → Over (Spec (.of K)))
    (p : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ V₀ j)
    (c : ∀ j, V₀ j ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))

private def borelPolynomialLeg (s : {s : Finset I // s.Nonempty})
    (j : ULift.{u} (Fin 2)) :
    Spec (.of (Polynomial (F.obj s))) ⟶ bsdhScheme G (word ++ [i]) :=
  projectiveLinePolynomialChart (F.obj s) j ≫
    projectiveAppendChart G i (F.obj s)
      (p s (sel s).val (sel s).property) (c (sel s).val)

variable (D : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ Scheme.{u})
    (eP : ∀ s, D.obj (op s) ≅ projectiveScheme (N.obj s) (ULift.{u} (Fin 2)))
    (cD : Cocone D) (hOpen : ∀ s, IsOpenImmersion (cD.ι.app s))
    (hCover : ∀ (Z : Scheme.{u}) (f : Z ⟶ cD.pt) (z : Z),
      ∃ s, ∃ x : (pullback f (cD.ι.app s) : Scheme.{u}),
        pullback.fst f (cD.ι.app s) x = z)
    (base : cD.pt ⟶ Spec (.of S))
    (m : bsdhScheme G (word ++ [i]) ⟶ cD.pt)
    (h₀ : IsPullback m (bsdhToSpec G (word ++ [i])) base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (b : ∀ s, Spec (.of (F.obj s)) ⟶ bsdhScheme G word)
    (hbbase : ∀ s, b s ≫ bsdhToSpec G word =
      Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s))))
    (hfield : ∀ s j, borelPolynomialLeg G word i F sel V₀ p c s j ≫ m =
      polynomialSpecMap (initialCoefficient (e s)) ≫
        (projectiveLinePolynomialChart (N.obj s) j ≫ (eP s).inv ≫ cD.ι.app (op s)))
    (hprior : ∀ s j, borelPolynomialLeg G word i F sel V₀ p c s j ≫
      bsdhAppendFst G word i =
        Spec.map (CommRingCat.ofHom (Polynomial.C : F.obj s →+* Polynomial (F.obj s))) ≫ b s)

include hbbase hprior in
private theorem borel_polynomial_base (s : {s : Finset I // s.Nonempty})
    (j : ULift.{u} (Fin 2)) :
    borelPolynomialLeg G word i F sel V₀ p c s j ≫
      bsdhToSpec G (word ++ [i]) =
        Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial (F.obj s)))) := by
  rw [← bsdhAppendFst_toSpec G word i]
  exact polynomial_chart_structure (borelPolynomialLeg G word i F sel V₀ p c s j)
    (bsdhAppendFst G word i) (bsdhToSpec G word) (b s) (hprior s j) (hbbase s)

variable {Y H Z : Scheme.{u}}
    (baseR : H ⟶ Spec (.of R)) (baseK : Z ⟶ Spec (.of K))
    (E : Z ≅ bsdhScheme G (word ++ [i]))
    (r : Z ⟶ bsdhScheme G (word ++ [i])) (hEr : E.hom = r)
    (hE : E.hom ≫ bsdhToSpec G (word ++ [i]) = baseK)
    (q₁ : Y ⟶ cD.pt) (q₂ : H ⟶ Y)
    (n : Z ⟶ H) (m₁ : bsdhScheme G (word ++ [i]) ⟶ Y)
    (hn : n ≫ q₂ = E.hom ≫ m₁) (hm : m₁ ≫ q₁ = m)
    (hK : IsPullback n baseK baseR
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (V₁ : Y.OpenCover.{u})
    (index₁ : V₁.I₀ ≃ (appendPolynomialCover N D eP cD hOpen hCover).I₀)
    (eV₁ : ∀ j, V₁.X j ≅
      Spec (.of (Polynomial (T ⊗[S] N.obj (index₁ j).1))))
    (hV₁ : ∀ j, V₁.f j ≫ q₁ = (eV₁ j).hom ≫
      polynomialSpecMap (Algebra.TensorProduct.includeRight :
        N.obj (index₁ j).1 →ₐ[S] T ⊗[S] N.obj (index₁ j).1).toRingHom ≫
          (appendPolynomialCover N D eP cD hOpen hCover).f (index₁ j))
    (V : H.OpenCover.{u}) (index₂ : V.I₀ ≃ V₁.I₀)
    (eV : ∀ j, V.X j ≅
      Spec (.of (Polynomial (R ⊗[T] (T ⊗[S] N.obj (index₁ (index₂ j)).1)))))
    (hV : ∀ j, V.f j ≫ q₂ = (eV j).hom ≫
      polynomialSpecMap (Algebra.TensorProduct.includeRight :
        T ⊗[S] N.obj (index₁ (index₂ j)).1 →ₐ[T]
          R ⊗[T] (T ⊗[S] N.obj (index₁ (index₂ j)).1)).toRingHom ≫
            (eV₁ (index₂ j)).inv ≫ V₁.f (index₂ j))
    (hVbase : ∀ j, V.f j ≫ baseR = (eV j).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Polynomial (R ⊗[T] (T ⊗[S] N.obj (index₁ (index₂ j)).1))))))
    [H.IsSeparated] [Smooth baseR]
    (W : H.OpenCover.{u}) [Finite W.I₀] [Finite V.I₀]
    [∀ w, IsAffine (W.X w)] [∀ j, IsAffine (V.X j)]

include base h₀ b hbbase hfield hprior hEr hE hn hm hV₁ hV hVbase in
/-- Construct the common-cover field maps into the Borel polynomial append charts. -/
theorem append_borel_matching_charts (hR : Function.Injective (algebraMap R K)) :
    let U := appendPolynomialCover N D eP cD hOpen hCover
    let jK := fun j : U.I₀ =>
      borelPolynomialLeg G word i F sel V₀ p c j.1 j.2 ≫ E.inv
    (∀ j, jK j ≫ r = borelPolynomialLeg G word i F sel V₀ p c j.1 j.2) ∧
    appendMatchingChartSpec baseR baseK n hK U
      (fun j => N.obj j.1) (fun j => F.obj j.1) (fun j => e j.1)
      V₁ index₁ V index₂ eV jK W hR := by
  let U := appendPolynomialCover N D eP cD hOpen hCover
  let jK := fun j : U.I₀ =>
    borelPolynomialLeg G word i F sel V₀ p c j.1 j.2 ≫ E.inv
  have hOld := iso_source_square E m (bsdhToSpec G (word ++ [i]))
    baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))) hE h₀
  have hWord : ∀ j, jK j ≫ r =
      borelPolynomialLeg G word i F sel V₀ p c j.1 j.2 :=
    fun j => iso_chart_word E _ r hEr
  refine ⟨hWord, ?_⟩
  exact append_matching_field_charts base baseR baseK q₁ q₂ n
    (E.hom ≫ m₁) (E.hom ≫ m) hK hOld hn
    (iso_prior_projection E m₁ q₁ m hm)
    U (fun j => N.obj j.1) (fun j => F.obj j.1) (fun j => e j.1)
    (fun j => Iso.refl _) V₁ index₁ eV₁ hV₁ V index₂ eV hV hVbase jK
    (fun j => iso_chart_projection E _ m _ (hfield j.1 j.2))
    (fun j => iso_chart_base E _ (bsdhToSpec G (word ++ [i])) baseK _ hE
      (borel_polynomial_base G word i F sel V₀ p c b hbbase hprior j.1 j.2))
    W hR

end BorelCharts

end SchubertGeometry
