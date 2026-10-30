import OrbitComplexity.SchubertGeometry.Frobenius.ProjectiveCovariance
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedPullback
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorMorphisms
import OrbitComplexity.FrobeniusSplitting.Cartier.ChartComposition
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Projective operator comparison from polynomial charts

The first polynomial chart of a projective line is scheme-theoretically
dense over every coefficient ring. Its pullback therefore detects equality
of sheaf operators, including their values along infinity. A commuting
polynomial operator square gives the entire projective comparison.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting
namespace SchubertGeometry.ProjectiveCartier
universe u

open private line indices chartOpen sourceLine sectionWeight
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator
open private chart_openPullback
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedPullback
open private projectiveChart_schematicallyDominant
  from OrbitComplexity.SchubertGeometry.Frobenius.ProjectiveCovariance

private theorem dense_chart_injective {X S : Scheme.{u}} {p : ℕ}
    (i : S ⟶ X) [IsOpenImmersion i] [IsSchemeTheoreticallyDominant i] [QuasiCompact i] :
    Function.Injective (fun φ : SchemeFrobeniusMap X p => φ.openPullback i) := by
  intro φ ψ h
  apply SchemeFrobeniusMap.ext
  intro U s
  apply i.app_injective U
  exact (φ.openPullback_natural i U s).symm.trans
    ((congrArg (fun τ : SchemeFrobeniusMap S p =>
      τ.onOpen (i ⁻¹ᵁ U) (i.app U s)) h).trans
        (ψ.openPullback_natural i U s))

private theorem openPullback_congr {X Y : Scheme.{u}} {p : ℕ}
    (φ : SchemeFrobeniusMap Y p) (f g : X ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    φ.openPullback f = φ.openPullback g := by
  subst g
  rfl

private theorem operator_map_from_chart {X Y S T : Scheme.{u}} {p : ℕ}
    (i : S ⟶ X) (j : T ⟶ Y) (f : X ⟶ Y) (a : S ⟶ T)
    [IsOpenImmersion i] [IsSchemeTheoreticallyDominant i] [QuasiCompact i]
    [IsOpenImmersion j] [IsOpenImmersion f] [IsOpenImmersion a]
    (hchart : a ≫ j = i ≫ f)
    (φ : SchemeFrobeniusMap X p) (ψ : SchemeFrobeniusMap Y p)
    (σ : SchemeFrobeniusMap S p) (τ : SchemeFrobeniusMap T p)
    (hφ : φ.openPullback i = σ) (hψ : ψ.openPullback j = τ)
    (ha : τ.openPullback a = σ) : ψ.openPullback f = φ := by
  apply dense_chart_injective i
  calc
    (ψ.openPullback f).openPullback i = ψ.openPullback (i ≫ f) :=
      (SchemeFrobeniusMap.openPullback_comp ψ i f).symm
    _ = ψ.openPullback (a ≫ j) := openPullback_congr ψ _ _ hchart.symm
    _ = (ψ.openPullback j).openPullback a :=
      SchemeFrobeniusMap.openPullback_comp ψ a j
    _ = τ.openPullback a := congrArg (fun θ : SchemeFrobeniusMap T p => θ.openPullback a) hψ
    _ = σ := ha
    _ = φ.openPullback i := hφ.symm

section Polynomial
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    {p : ℕ} [ExpChar K p] [PerfectRing K p]

private theorem relativeCartier_open_chart (ψ : FrobeniusLinearMap A p)
    (s : (sourceLine A p).val.obj (op ⊤)) (j : indices.{u}) :
    (relativeCartierOperator (K := K) ψ s).openPullback
        (projectiveLinePolynomialChart A j) =
      ((polynomialTraceOfOperator (K := K) ψ).weight (sectionWeight s j)).toSpec
        (expChar_pos K p) := by
  have h := relativeCartierOperator_chart (K := K) ψ s j
  exact chart_openPullback (chartOpen A j) (projectiveLinePolynomialIso A j)
    (relativeCartierOperator (K := K) ψ s)
    (((polynomialTraceOfOperator (K := K) ψ).weight (sectionWeight s j)).toSpec
      (expChar_pos K p)) h

/-- A polynomial-chart square commuting with the determinant-weighted traces
identifies the complete projective Cartier operators, including infinity. -/
theorem relativeCartierOperator_map {B : Type u} [CommRing B] [Algebra K B]
    (ψA : FrobeniusLinearMap A p) (ψB : FrobeniusLinearMap B p)
    (sA : (sourceLine A p).val.obj (op ⊤))
    (sB : (sourceLine B p).val.obj (op ⊤))
    (α : Polynomial A →+* Polynomial B) (f : line B ⟶ line A)
    [IsOpenImmersion f] [IsOpenImmersion (Spec.map (CommRingCat.ofHom α))]
    (hchart : Spec.map (CommRingCat.ofHom α) ≫ projectiveLinePolynomialChart A ⟨0⟩ =
      projectiveLinePolynomialChart B ⟨0⟩ ≫ f)
    (htrace : ∀ Q,
      ((polynomialTraceOfOperator (K := K) ψB).weight (sectionWeight sB ⟨0⟩)) (α Q) =
        α (((polynomialTraceOfOperator (K := K) ψA).weight (sectionWeight sA ⟨0⟩)) Q)) :
    (relativeCartierOperator (K := K) ψA sA).openPullback f =
      relativeCartierOperator (K := K) ψB sB := by
  let := projectiveChart_schematicallyDominant B
  let : QuasiCompact (projectiveLinePolynomialChart B (⟨0⟩ : indices.{u})) := inferInstance
  have ha := SchemeFrobeniusMap.openPullback_eq_of_commute
    (((polynomialTraceOfOperator (K := K) ψA).weight (sectionWeight sA ⟨0⟩)).toSpec
      (expChar_pos K p))
    (((polynomialTraceOfOperator (K := K) ψB).weight (sectionWeight sB ⟨0⟩)).toSpec
      (expChar_pos K p)) (Spec.map (CommRingCat.ofHom α))
    (FrobeniusLinearMap.toSpec_naturality _ _ (expChar_pos K p) α htrace)
  exact operator_map_from_chart
    (projectiveLinePolynomialChart B ⟨0⟩) (projectiveLinePolynomialChart A ⟨0⟩)
    f (Spec.map (CommRingCat.ofHom α)) hchart
    (relativeCartierOperator (K := K) ψB sB)
    (relativeCartierOperator (K := K) ψA sA) _ _
    (relativeCartier_open_chart (K := K) ψB sB ⟨0⟩)
    (relativeCartier_open_chart (K := K) ψA sA ⟨0⟩) ha
end Polynomial
end SchubertGeometry.ProjectiveCartier
