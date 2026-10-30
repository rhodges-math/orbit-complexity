import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.FramedOperatorMaps
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedGlobal
import OrbitComplexity.FrobeniusSplitting.Cartier.OpenCoframes
import OrbitComplexity.FrobeniusSplitting.Cartier.ChartComposition
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Cartier morphisms on charts of the matching line

The relative Cartier morphism is expressed in its polynomial coframe and
transported through the common polynomial chart to the specified matching
line. This construction transports the morphism before section insertion.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

open private pullback_eq_of_hom_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedComparison

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def commonChartMap {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {A X Y : Scheme.{u}} (baseX : X ⟶ Spec (.of C))
    (baseY : Y ⟶ Spec (.of C)) (L : X.Modules) (M : Y.Modules)
    (k : A ⟶ X) (j : A ⟶ Y) [IsOpenImmersion k] [IsOpenImmersion j]
    (F : (pullback k).obj L ≅ unitModule A)
    (E : (pullback j).obj M ≅ unitModule A)
    (Θ : frobeniusRestriction C p baseY M ⟶ unitModule Y) :
    (frobeniusRestriction C p baseX L).over k.opensRange ⟶
      (unitModule X).over k.opensRange :=
  let e : k.opensRange.toScheme ≅ j.opensRange.toScheme :=
    k.isoOpensRange.symm ≪≫ j.isoOpensRange
  coframedOpenMap baseX L k.opensRange (coframeOverRange k L F)
    ((framedOpenOperator baseY M j.opensRange (coframeOverRange j M E)
      (Θ.over j.opensRange)).openPullback e.hom)

private def commonChartData {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {A X Y : Scheme.{u}} (baseX : X ⟶ Spec (.of C))
    (baseY : Y ⟶ Spec (.of C)) (L : X.Modules) (M : Y.Modules)
    (k : A ⟶ X) (j : A ⟶ Y) [IsOpenImmersion k] [IsOpenImmersion j]
    (F : (pullback k).obj L ≅ unitModule A)
    (E : (pullback j).obj M ≅ unitModule A)
    (Θ : frobeniusRestriction C p baseY M ⟶ unitModule Y)
    (H : (frobeniusRestriction C p baseX L).over k.opensRange ⟶
      (unitModule X).over k.opensRange) : Prop :=
  (framedOpenOperator baseX L k.opensRange (coframeOverRange k L F) H).openPullback
      k.isoOpensRange.hom =
    (framedOpenOperator baseY M j.opensRange (coframeOverRange j M E)
      (Θ.over j.opensRange)).openPullback j.isoOpensRange.hom

private theorem commonChartMap_coordinate {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {A X Y : Scheme.{u}}
    (baseX : X ⟶ Spec (.of C)) (baseY : Y ⟶ Spec (.of C))
    (L : X.Modules) (M : Y.Modules) (k : A ⟶ X) (j : A ⟶ Y)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (F : (pullback k).obj L ≅ unitModule A)
    (E : (pullback j).obj M ≅ unitModule A)
    (Θ : frobeniusRestriction C p baseY M ⟶ unitModule Y) :
    commonChartData baseX baseY L M k j F E Θ
      (commonChartMap baseX baseY L M k j F E Θ) := by
  unfold commonChartData commonChartMap
  rw [framedOpenOperator_coframed, ← SchemeFrobeniusMap.openPullback_comp]
  have h : k.isoOpensRange.hom ≫
      (k.isoOpensRange.symm ≪≫ j.isoOpensRange).hom = j.isoOpensRange.hom := by
    simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  exact pullback_eq_of_hom_eq
    (framedOpenOperator baseY M j.opensRange (coframeOverRange j M E)
      (Θ.over j.opensRange)) h

open private indices line chart chartOpen relativeBase sourceLine from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

private def polynomialCoframe (A : Type u) [CommRing A] (p : ℕ) (j : indices.{u}) :
    (pullback (chart A j)).obj (sourceLine (A := A) (p := p)) ≅
      unitModule (Spec (.of (Polynomial A))) :=
  ((restrictFunctorIsoPullback (chart A j)).app (sourceLine (A := A) (p := p))).symm ≪≫
    SchubertGeometry.ProjectiveLine.projectiveTransitionChart A (p - 1) j

/-- Transfer the specified relative Cartier morphism to a polynomial chart of
the matching line, using its given coframe. -/
def relativeCartierWordChart {K : Type u} [Field K] {p : ℕ} [ExpChar K p]
    [PerfectRing K p] {A : Type u} [CommRing A] [Algebra K A]
    (ψ : FrobeniusLinearMap A p) (j : indices.{u}) {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (L : X.Modules)
    (k : Spec (.of (Polynomial A)) ⟶ X) [IsOpenImmersion k]
    (F : (pullback k).obj L ≅ unitModule (Spec (.of (Polynomial A)))) :
    (frobeniusRestriction K p base L).over k.opensRange ⟶
      (unitModule X).over k.opensRange :=
  commonChartMap base (relativeBase (K := K) (A := A)) L
    (sourceLine (A := A) (p := p)) k (chart A j) F (polynomialCoframe A p j)
    (relativeTwistedCartierMap (K := K) ψ)

/-- In the polynomial coordinate, the matching-line chart map retains the
original relative Cartier morphism before insertion of a section. -/
theorem relativeCartierWordChart_coordinate {K : Type u} [Field K]
    {p : ℕ} [ExpChar K p] [PerfectRing K p] {A : Type u} [CommRing A] [Algebra K A]
    (ψ : FrobeniusLinearMap A p) (j : indices.{u}) {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (L : X.Modules)
    (k : Spec (.of (Polynomial A)) ⟶ X) [IsOpenImmersion k]
    (F : (pullback k).obj L ≅ unitModule (Spec (.of (Polynomial A)))) :
    commonChartData base (relativeBase (K := K) (A := A)) L
      (sourceLine (A := A) (p := p)) k (chart A j) F (polynomialCoframe A p j)
      (relativeTwistedCartierMap (K := K) ψ)
      (relativeCartierWordChart ψ j base L k F) :=
  commonChartMap_coordinate base (relativeBase (K := K) (A := A)) L
    (sourceLine (A := A) (p := p)) k (chart A j) F (polynomialCoframe A p j)
    (relativeTwistedCartierMap (K := K) ψ)

end SchubertGeometry.ProjectiveCartier
