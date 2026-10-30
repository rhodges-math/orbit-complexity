import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierSections
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Polynomial coordinates for a word Cartier chart

The polynomial section and its standard coframe are compared before the chart
map is substituted. The raw map is then identified by a whole-map equation.
-/

set_option autoImplicit false
noncomputable section
universe u v w v' w'

open AlgebraicGeometry CategoryTheory Opposite
open FrobeniusSplitting

namespace SchubertGeometry.ProjectiveCartier

open private line chart sourceLine relativeBase from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private polynomialCoframe commonChartMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierCharts
open private sectionValue polynomial_chart_section from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
open private insertedInfinity from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections
open private chartInsertedData commonChartMap_insert from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierSections

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def framedSectionValue {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules) (m : unitModule Y ⟶ M)
    (F : (Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit X.ringCatSheaf)
    (a : Γ(X, ⊤)) : Prop :=
  sectionValue f M m F.hom a

private theorem iso_symm_app {C : Type v} [Category.{w} C]
    {D : Type v'} [Category.{w'} D] {F G : C ⥤ D} (e : F ≅ G) (M : C) :
    e.symm.app M = (e.app M).symm := rfl

private theorem restrictionFrame_hom {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (T : M.restrict f ≅ SheafOfModules.unit X.ringCatSheaf)
    (F : (Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit X.ringCatSheaf)
    (hF : F = ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm ≪≫ T) :
    ((Scheme.Modules.restrictFunctorIsoPullback f).symm.app M).hom ≫ T.hom = F.hom := by
  subst F
  have hR := iso_symm_app (Scheme.Modules.restrictFunctorIsoPullback f) M
  exact congrArg (fun R : (Scheme.Modules.pullback f).obj M ≅ M.restrict f =>
    R.hom ≫ T.hom) hR

private theorem sectionValue_hom_eq {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules) (m : unitModule Y ⟶ M)
    (e₀ e₁ : (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (a : Γ(X, ⊤)) (he : e₀ = e₁) (hs : sectionValue f M m e₀ a) :
    sectionValue f M m e₁ a := by
  subst e₁
  exact hs

private theorem restrictionFrame_section {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (m : unitModule Y ⟶ M)
    (T : M.restrict f ≅ SheafOfModules.unit X.ringCatSheaf)
    (F : (Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit X.ringCatSheaf)
    (a : Γ(X, ⊤))
    (hF : F = ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm ≪≫ T)
    (hs : sectionValue f M m
      (((Scheme.Modules.restrictFunctorIsoPullback f).symm.app M).hom ≫ T.hom) a) :
    framedSectionValue f M m F a := by
  exact sectionValue_hom_eq f M m _ F.hom a (restrictionFrame_hom f M T F hF) hs

private theorem commonChartMap_insert_framed {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {A X Y : Scheme.{u}}
    (baseX : X ⟶ Spec (.of C)) (baseY : Y ⟶ Spec (.of C))
    (L : X.Modules) (M : Y.Modules) (k : A ⟶ X) (j : A ⟶ Y)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (F : (Scheme.Modules.pullback k).obj L ≅ unitModule A)
    (E : (Scheme.Modules.pullback j).obj M ≅ unitModule A)
    (Θ : frobeniusRestriction C p baseY M ⟶ unitModule Y)
    (mX : unitModule X ⟶ L) (mY : unitModule Y ⟶ M) (a : Γ(A, ⊤))
    (hs : sectionValue k L mX F.hom a) (ht : framedSectionValue j M mY E a)
    (Φ : SchemeFrobeniusMap Y p)
    (hΦ : twistedSectionOperator baseY M Θ
      ((mY.val.app (op ⊤)).hom (1 : Γ(Y, ⊤))) = Φ) :
    chartInsertedData baseX L k (commonChartMap baseX baseY L M k j F E Θ) mX Φ j := by
  exact commonChartMap_insert baseX baseY L M k j F E Θ mX mY a hs ht Φ hΦ

private theorem polynomialSource_value {A : Type u} [CommRing A]
    (p : ℕ) (W : Polynomial A) (hW : W.natDegree ≤ p - 1)
    (j : ULift.{u} (Fin 2)) :
    framedSectionValue (projectiveLinePolynomialChart A j)
      (ProjectiveLine.projectiveTransitionModule A (p - 1))
      (ProjectiveLine.projectivePolynomialSection A (p - 1) W hW)
      (polynomialCoframe A p j)
      ((Scheme.ΓSpecIso (.of (Polynomial A))).inv
        (RetainedCharacter.sectionChartPolynomial (p - 1) W j.down)) := by
  rcases j with ⟨j⟩
  let f := projectiveLinePolynomialChart A (⟨j⟩ : ULift.{u} (Fin 2))
  let M := ProjectiveLine.projectiveTransitionModule A (p - 1)
  let T := ProjectiveLine.projectiveTransitionChart A (p - 1) ⟨j⟩
  have leaf := restrictionFrame_section f M
    (ProjectiveLine.projectivePolynomialSection A (p - 1) W hW) T
    (polynomialCoframe A p ⟨j⟩)
    ((Scheme.ΓSpecIso (.of (Polynomial A))).inv
      (RetainedCharacter.sectionChartPolynomial (p - 1) W j))
  exact leaf rfl (polynomial_chart_section A (p - 1) W hW j)

/-- A polynomial section coordinate identifies the inserted chart operator with
the relative Cartier operator of that polynomial. The raw chart map is retained
through its whole-map equation. -/
theorem relativePolynomialChart_section {K : Type u} [Field K]
    {p : ℕ} [ExpChar K p] [PerfectRing K p]
    {A : Type u} [CommRing A] [Algebra K A]
    (ψ : FrobeniusLinearMap A p) (j : ULift.{u} (Fin 2)) {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (L : X.Modules)
    (k : Spec (.of (Polynomial A)) ⟶ X) [IsOpenImmersion k]
    (F : (Scheme.Modules.pullback k).obj L ≅ unitModule (Spec (.of (Polynomial A))))
    (H : (frobeniusRestriction K p base L).over k.opensRange ⟶
      (unitModule X).over k.opensRange)
    (hH : H = relativeCartierWordChart ψ j base L k F)
    (m : unitModule X ⟶ L)
    (W : Polynomial A) (hW : W.natDegree ≤ p - 1)
    (hs : sectionValue k L m F.hom
      ((Scheme.ΓSpecIso (.of (Polynomial A))).inv
        (RetainedCharacter.sectionChartPolynomial (p - 1) W j.down))) :
    chartInsertedData base L k H m
      (relativeCartierOperator (K := K) ψ (insertedInfinity
        (ProjectiveLine.projectivePolynomialSection A (p - 1) W hW))) (chart A j) := by
  subst H
  have ht := polynomialSource_value p W hW j
  exact commonChartMap_insert_framed base (relativeBase (K := K) (A := A)) L
    (sourceLine (A := A) (p := p)) k (chart A j) F (polynomialCoframe A p j)
    (relativeTwistedCartierMap (K := K) ψ) m
    (ProjectiveLine.projectivePolynomialSection A (p - 1) W hW)
    ((Scheme.ΓSpecIso (.of (Polynomial A))).inv
      (RetainedCharacter.sectionChartPolynomial (p - 1) W j.down)) hs ht
    (relativeCartierOperator (K := K) ψ (insertedInfinity
      (ProjectiveLine.projectivePolynomialSection A (p - 1) W hW)))
    (twistedSectionOperator_relative (K := K) ψ
      (ProjectiveLine.projectivePolynomialSection A (p - 1) W hW))

end SchubertGeometry.ProjectiveCartier
