import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierCharts
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.FramedSectionOperators
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CoframeSectionCoordinates
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.OpenSectionOperators
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSection
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Section insertion on the polynomial charts of the matching line

The matching-line section and the projective-line section have the same
polynomial coefficient. Consequently the transported raw Cartier morphism,
with the matching section inserted once, is the prescribed relative Cartier
operator on the common polynomial chart.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

open private twistedOverMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private commonChartMap commonChartData commonChartMap_coordinate polynomialCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierCharts
open private chartCoefficientData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CoframeSectionCoordinates
open private pullback_eq_of_hom_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedComparison

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def insertedChartOperator {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules) (U : X.Opens)
    (m : unitModule X ⟶ L)
    (H : (frobeniusRestriction C p base L).over U ⟶ (unitModule X).over U) :
    SchemeFrobeniusMap U.toScheme p :=
  openOperatorEquiv C p base U (twistedOverMap base (unitModule X) L U (m.over U) ≫ H)

private def chartInsertedData {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {A X Y : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (k : A ⟶ X) [IsOpenImmersion k]
    (H : (frobeniusRestriction C p base L).over k.opensRange ⟶
      (unitModule X).over k.opensRange)
    (m : unitModule X ⟶ L) (Φ : SchemeFrobeniusMap Y p)
    (j : A ⟶ Y) [IsOpenImmersion j] : Prop :=
  (insertedChartOperator base L k.opensRange m H).openPullback k.isoOpensRange.hom =
    Φ.openPullback j

private theorem commonChartMap_insert {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {A X Y : Scheme.{u}}
    (baseX : X ⟶ Spec (.of C)) (baseY : Y ⟶ Spec (.of C))
    (L : X.Modules) (M : Y.Modules) (k : A ⟶ X) (j : A ⟶ Y)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (F : (pullback k).obj L ≅ unitModule A)
    (E : (pullback j).obj M ≅ unitModule A)
    (Θ : frobeniusRestriction C p baseY M ⟶ unitModule Y)
    (mX : unitModule X ⟶ L) (mY : unitModule Y ⟶ M)
    (a : Γ(A, ⊤))
    (hs : ((pullbackObjUnitIso k).inv ≫ (pullback k).map mX) ≫ F.hom =
      globalSectionsSmul (unitModule A) a)
    (ht : ((pullbackObjUnitIso j).inv ≫ (pullback j).map mY) ≫ E.hom =
      globalSectionsSmul (unitModule A) a)
    (Φ : SchemeFrobeniusMap Y p)
    (hΦ : twistedSectionOperator baseY M Θ
      ((mY.val.app (op ⊤)).hom (1 : Γ(Y, ⊤))) = Φ) :
    chartInsertedData baseX L k
      (commonChartMap baseX baseY L M k j F E Θ) mX Φ j := by
  let U := k.opensRange
  let V := j.opensRange
  let FK := coframeOverRange k L F
  let EJ := coframeOverRange j M E
  let H := commonChartMap baseX baseY L M k j F E Θ
  let cX : Γ(X, U) := ((mX.over U ≫ FK.hom).val.app (op (Over.mk (𝟙 U)))).hom
    (1 : Γ(X, U))
  let cY : Γ(Y, V) := ((mY.over V ≫ EJ.hom).val.app (op (Over.mk (𝟙 V)))).hom
    (1 : Γ(Y, V))
  have hcx : k.isoOpensRange.hom.appTop (U.topIso.inv cX) = a :=
    coframeRange_section_coefficient k L mX F a hs
  have hcy : j.isoOpensRange.hom.appTop (V.topIso.inv cY) = a :=
    coframeRange_section_coefficient j M mY E a ht
  have hraw := commonChartMap_coordinate baseX baseY L M k j F E Θ
  change (framedOpenOperator baseX L U FK H).openPullback k.isoOpensRange.hom =
    (framedOpenOperator baseY M V EJ (Θ.over V)).openPullback j.isoOpensRange.hom at hraw
  have hiX := congrArg (fun φ : SchemeFrobeniusMap U.toScheme p =>
    φ.openPullback k.isoOpensRange.hom) (coframeInsertion_operator baseX L U FK (mX.over U) H)
  have hiY := congrArg (fun φ : SchemeFrobeniusMap V.toScheme p =>
    φ.openPullback j.isoOpensRange.hom)
      (coframeInsertion_operator baseY M V EJ (mY.over V) (Θ.over V))
  have hx := (framedOpenOperator baseX L U FK H).openPullback_inputWeight
    k.isoOpensRange.hom (U.topIso.inv cX)
  have hy := (framedOpenOperator baseY M V EJ (Θ.over V)).openPullback_inputWeight
    j.isoOpensRange.hom (V.topIso.inv cY)
  have hweight := congrArg₂ (fun (φ : SchemeFrobeniusMap A p) (b : Γ(A, ⊤)) =>
    φ.inputWeight b) hraw (hcx.trans hcy.symm)
  have hlocal : (insertedChartOperator baseX L U mX H).openPullback
      k.isoOpensRange.hom =
      (insertedChartOperator baseY M V mY (Θ.over V)).openPullback j.isoOpensRange.hom :=
    hiX.trans (hx.trans (hweight.trans (hy.symm.trans hiY.symm)))
  have hyGlobal := congrArg (fun φ : SchemeFrobeniusMap V.toScheme p =>
    φ.openPullback j.isoOpensRange.hom)
      (twistedSectionOperator_onOpen baseY M Θ mY V)
  have hglobal := congrArg (fun φ : SchemeFrobeniusMap Y p =>
    (φ.restrict V).openPullback j.isoOpensRange.hom) hΦ
  have hchart : (Φ.restrict V).openPullback j.isoOpensRange.hom = Φ.openPullback j := by
    calc
      _ = (Φ.openPullback V.ι).openPullback j.isoOpensRange.hom :=
        congrArg (fun φ : SchemeFrobeniusMap V.toScheme p =>
          φ.openPullback j.isoOpensRange.hom) (Φ.openPullback_restrict V).symm
      _ = Φ.openPullback (j.isoOpensRange.hom ≫ V.ι) :=
        (Φ.openPullback_comp j.isoOpensRange.hom V.ι).symm
      _ = Φ.openPullback j := pullback_eq_of_hom_eq Φ j.isoOpensRange_hom_ι
  exact hlocal.trans (hyGlobal.trans (hglobal.trans hchart))

open private indices line chart relativeBase sourceLine from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private insertedInfinity from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections

/-- Inserting equal polynomial coordinates of the two sections identifies
the word-chart operator with the original relative Cartier operator. -/
theorem relativeCartierWordChart_section {K : Type u} [Field K]
    {p : ℕ} [ExpChar K p] [PerfectRing K p] {A : Type u} [CommRing A] [Algebra K A]
    (ψ : FrobeniusLinearMap A p) (j : indices.{u}) {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (L : X.Modules)
    (k : Spec (.of (Polynomial A)) ⟶ X) [IsOpenImmersion k]
    (F : (pullback k).obj L ≅ unitModule (Spec (.of (Polynomial A))))
    (mX : unitModule X ⟶ L)
    (mY : unitModule (line A) ⟶ sourceLine (A := A) (p := p))
    (a : Γ(Spec (.of (Polynomial A)), ⊤))
    (hs : ((pullbackObjUnitIso k).inv ≫ (pullback k).map mX) ≫ F.hom =
      globalSectionsSmul (unitModule (Spec (.of (Polynomial A)))) a)
    (ht : ((pullbackObjUnitIso (chart A j)).inv ≫ (pullback (chart A j)).map mY) ≫
      (polynomialCoframe A p j).hom =
        globalSectionsSmul (unitModule (Spec (.of (Polynomial A)))) a) :
    chartInsertedData base L k (relativeCartierWordChart ψ j base L k F) mX
      (relativeCartierOperator (K := K) ψ (insertedInfinity mY)) (chart A j) :=
  commonChartMap_insert base (relativeBase (K := K) (A := A)) L
    (sourceLine (A := A) (p := p)) k (chart A j) F (polynomialCoframe A p j)
    (relativeTwistedCartierMap (K := K) ψ) mX mY a hs ht
    (relativeCartierOperator (K := K) ψ (insertedInfinity mY))
    (twistedSectionOperator_relative (K := K) ψ mY)

end SchubertGeometry.ProjectiveCartier
