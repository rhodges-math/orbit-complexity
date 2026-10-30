import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CartesianCoframeComparison
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Scalar comparison of whole polynomial coframes

The constructed coframe on a whole polynomial chart retains the prescribed
scalar comparison with the coframe built from the same word-line
isomorphism and polynomial coframe.
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.OperatorSheaf

open private square_b_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCoframePairs
open private wholeComparison comparedWholeFrame comparedFineFrame
  polynomialCover_map polynomialFine_square polynomialFineCoframe
  restrictedFineFrame_comparison from
    OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes

namespace SchubertGeometry

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- A polynomial-chart coframe with its prescribed fine restrictions and scalar comparison. -/
def polynomialCoframeComparison {P PK : Scheme.{u}} (z : PK ⟶ P)
    (U : P.OpenCover.{u}) (M : P.Modules)
    (E : ∀ w, (Scheme.Modules.pullback (U.f w)).obj M ≅ unitModule (U.X w))
    (FK : (Scheme.Modules.pullback z).obj M ≅ unitModule PK) : Prop :=
  ∃ F : M ≅ unitModule P,
    (∀ w, F.hom.over (U.f w).opensRange = (coframeOverRange (U.f w) M (E w)).hom ∧
      F.inv.over (U.f w).opensRange = (coframeOverRange (U.f w) M (E w)).inv) ∧
    (Scheme.Modules.pullback z).mapIso F ≪≫ pullbackObjUnitIso z = FK

/-- The whole polynomial coframe retains the same word-line comparison,
without adding a scalar-cover or overlap-compatibility hypothesis. -/
theorem commonPolynomialCoframe_compare {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (hR : Function.Injective (algebraMap R K))
    {Y YK PK Z : Scheme.{u}} [Y.IsSeparated]
    (base : Y ⟶ Spec (.of R)) [Smooth base]
    (W V : Y.OpenCover.{u}) [∀ w, IsAffine (W.X w)] [∀ v, IsAffine (V.X v)]
    (v : V.I₀) (q : YK ⟶ Y) (r : YK ⟶ Z) (g : PK ⟶ YK) (z : PK ⟶ V.X v)
    (hwhole : z ≫ V.f v = g ≫ q)
    (baseK : PK ⟶ Spec (.of K))
    (hfield : IsPullback z baseK (V.f v ≫ base)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (c : PK ⟶ Z) (h : g ≫ r = c)
    (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback q).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (Epoly : (Scheme.Modules.pullback c).obj LK ≅ unitModule PK)
    (A : W.I₀ → Scheme.{u}) (a : ∀ w, A w ⟶ PK)
    (u : ∀ w, A w ⟶ (commonPolynomialCover W V v).X w)
    (hchart : ∀ w, IsPullback (u w) (a w) ((commonPolynomialCover W V v).f w) z)
    (E : ∀ w : W.I₀,
      (Scheme.Modules.pullback ((appendCommonCover W V).f ⟨w, v⟩)).obj L ≅
        unitModule ((commonPolynomialCover W V v).X w))
    (he : ∀ w, squareFrameIso q (a w ≫ g) ((appendCommonCover W V).f ⟨w, v⟩)
        (u w) (polynomialFine_square W V v w q g z hwhole (a w) (u w) (hchart w).w)
        L (E w) = comparedFineFrame r g (a w) c
          ((Category.assoc (a w) g r).trans (congrArg (fun k => a w ≫ k) h))
          ((Scheme.Modules.pullback q).obj L) LK EL Epoly) :
    polynomialCoframeComparison z (commonPolynomialCover W V v)
      ((Scheme.Modules.pullback (V.f v)).obj L) (polynomialFineCoframe W V v L E)
      (wholeComparison q (V.f v) g z hwhole L ≪≫
        comparedWholeFrame r g c h ((Scheme.Modules.pullback q).obj L) LK EL Epoly) := by
  obtain ⟨F, hF⟩ := commonPolynomialCoframe_glue hR base W V v q r g z hwhole
    baseK hfield c h L LK EL Epoly A a u hchart E he
  refine ⟨F, hF, ?_⟩
  let U := commonPolynomialCover W V v
  let FK := wholeComparison q (V.f v) g z hwhole L ≪≫
    comparedWholeFrame r g c h ((Scheme.Modules.pullback q).obj L) LK EL Epoly
  have hcompare w : squareFrameIso z (a w) (U.f w) (u w) (hchart w).w
      ((Scheme.Modules.pullback (V.f v)).obj L) (polynomialFineCoframe W V v L E w) =
      (Scheme.Modules.pullback (a w)).mapIso FK ≪≫ pullbackObjUnitIso (a w) := by
    have ht : u w ≫ (U.f w ≫ V.f v) = (a w ≫ g) ≫ q := by
      rw [polynomialCover_map]
      exact polynomialFine_square W V v w q g z hwhole (a w) (u w) (hchart w).w
    have hc := square_b_eq q (a w ≫ g) (U.f w ≫ V.f v)
      ((appendCommonCover W V).f ⟨w, v⟩) (polynomialCover_map W V v w) (u w) ht
      (polynomialFine_square W V v w q g z hwhole (a w) (u w) (hchart w).w) L (E w)
    exact restrictedFineFrame_comparison q r (V.f v) g z (a w) (U.f w) (u w)
      hwhole (hchart w).w ht c h _ L LK EL Epoly
      ((pullbackCongr (polynomialCover_map W V v w)).app L ≪≫ E w) (hc.trans (he w))
  exact scalarCoframe_eq_of_squares z U A a u hchart
    ((Scheme.Modules.pullback (V.f v)).obj L) F FK (polynomialFineCoframe W V v L E)
    (fun w => (hF w).1) hcompare

end SchubertGeometry
