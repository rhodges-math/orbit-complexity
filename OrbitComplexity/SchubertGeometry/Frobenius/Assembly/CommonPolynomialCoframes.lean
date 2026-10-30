import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCover
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCoframeGluing
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareRebase
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ComparedCoframeRefinement
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coframes on whole polynomial charts

The coframes on the common matching refinement determine coframes on each
whole polynomial chart. Their scalar comparisons use the same line
isomorphism and polynomial coframe throughout.
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting.CharacterLine

open private square_b_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCoframePairs

namespace SchubertGeometry

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def comparedWholeFrame {YK PK Z : Scheme.{u}}
    (r : YK ⟶ Z) (g : PK ⟶ YK) (c : PK ⟶ Z) (h : g ≫ r = c)
    (M : YK.Modules) (LK : Z.Modules)
    (EL : M ≅ (Scheme.Modules.pullback r).obj LK)
    (E : (Scheme.Modules.pullback c).obj LK ≅ unitModule PK) :
    (Scheme.Modules.pullback g).obj M ≅ unitModule PK :=
  (Scheme.Modules.pullback g).mapIso EL ≪≫ (pullbackComp g r).app LK ≪≫
    (pullbackCongr h).app LK ≪≫ E

private def comparedFineFrame {YK PK Z A : Scheme.{u}}
    (r : YK ⟶ Z) (g : PK ⟶ YK) (a : A ⟶ PK) (c : PK ⟶ Z)
    (h : (a ≫ g) ≫ r = a ≫ c) (M : YK.Modules) (LK : Z.Modules)
    (EL : M ≅ (Scheme.Modules.pullback r).obj LK)
    (E : (Scheme.Modules.pullback c).obj LK ≅ unitModule PK) :
    (Scheme.Modules.pullback (a ≫ g)).obj M ≅ unitModule A :=
  (Scheme.Modules.pullback (a ≫ g)).mapIso EL ≪≫
    (pullbackComp (a ≫ g) r).app LK ≪≫ (pullbackCongr h).app LK ≪≫
    ((pullbackComp a c).app LK).symm ≪≫
    (Scheme.Modules.pullback a).mapIso E ≪≫ pullbackObjUnitIso a

private theorem comparedWholeFrame_refine {YK PK Z A : Scheme.{u}}
    (r : YK ⟶ Z) (g : PK ⟶ YK) (a : A ⟶ PK) (c : PK ⟶ Z)
    (h : g ≫ r = c) (hfine : (a ≫ g) ≫ r = a ≫ c)
    (M : YK.Modules) (LK : Z.Modules)
    (EL : M ≅ (Scheme.Modules.pullback r).obj LK)
    (E : (Scheme.Modules.pullback c).obj LK ≅ unitModule PK) :
    comparedFineFrame r g a c hfine M LK EL E =
      ((pullbackComp a g).app M).symm ≪≫
        (Scheme.Modules.pullback a).mapIso (comparedWholeFrame r g c h M LK EL E) ≪≫
        pullbackObjUnitIso a := by
  have hc := FrobeniusSplitting.RetainedCharacter.comparedCoframe_refine
    r (a ≫ g) g a c rfl h hfine M LK EL E
  exact hc.trans (Iso.refl_trans _)

private theorem refinement_cancel {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M N U : C} {P Q : D}
    (H : M ≅ N) (E : N ≅ U) (i : F.obj N ≅ P) (w : F.obj U ≅ Q) :
    F.mapIso H ≪≫ i ≪≫ (i.symm ≪≫ F.mapIso E ≪≫ w) =
      F.mapIso (H ≪≫ E) ≪≫ w := by
  ext
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

private def wholeComparison {Y YK P PK : Scheme.{u}}
    (q : YK ⟶ Y) (f : P ⟶ Y) (g : PK ⟶ YK) (z : PK ⟶ P)
    (h : z ≫ f = g ≫ q) (L : Y.Modules) :
    (Scheme.Modules.pullback z).obj ((Scheme.Modules.pullback f).obj L) ≅
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback q).obj L) :=
  (pullbackComp z f).app L ≪≫ (pullbackCongr h).app L ≪≫
    ((pullbackComp g q).app L).symm

private theorem restrictedFineFrame_comparison {Y YK P PK Z A B : Scheme.{u}}
    (q : YK ⟶ Y) (r : YK ⟶ Z) (f : P ⟶ Y) (g : PK ⟶ YK)
    (z : PK ⟶ P) (a : A ⟶ PK) (b : B ⟶ P) (u : A ⟶ B)
    (hwhole : z ≫ f = g ≫ q) (hsmall : u ≫ b = a ≫ z)
    (htotal : u ≫ (b ≫ f) = (a ≫ g) ≫ q)
    (c : PK ⟶ Z) (h : g ≫ r = c) (hfine : (a ≫ g) ≫ r = a ≫ c)
    (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback q).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (E : (Scheme.Modules.pullback c).obj LK ≅ unitModule PK)
    (F : (Scheme.Modules.pullback (b ≫ f)).obj L ≅ unitModule B)
    (he : squareFrameIso q (a ≫ g) (b ≫ f) u htotal L F =
      comparedFineFrame r g a c hfine ((Scheme.Modules.pullback q).obj L) LK EL E) :
    squareFrameIso z a b u hsmall ((Scheme.Modules.pullback f).obj L)
        ((pullbackComp b f).app L ≪≫ F) =
      (Scheme.Modules.pullback a).mapIso
          (wholeComparison q f g z hwhole L ≪≫
            comparedWholeFrame r g c h ((Scheme.Modules.pullback q).obj L) LK EL E) ≪≫
        pullbackObjUnitIso a := by
  have href := he.trans (comparedWholeFrame_refine r g a c h hfine
    ((Scheme.Modules.pullback q).obj L) LK EL E)
  have htransport := congrArg (fun H =>
    (Scheme.Modules.pullback a).mapIso (wholeComparison q f g z hwhole L) ≪≫
      (pullbackComp a g).app ((Scheme.Modules.pullback q).obj L) ≪≫ H) href
  exact (squareFrameIso_rebase q f g z a b u hwhole hsmall htotal L F).trans
    (htransport.trans (refinement_cancel (Scheme.Modules.pullback a)
      (wholeComparison q f g z hwhole L)
      (comparedWholeFrame r g c h ((Scheme.Modules.pullback q).obj L) LK EL E)
      ((pullbackComp a g).app ((Scheme.Modules.pullback q).obj L))
      (pullbackObjUnitIso a)))

private theorem polynomialCover_map {Y : Scheme.{u}} (W V : Y.OpenCover.{u})
    (v : V.I₀) (w : W.I₀) :
    (commonPolynomialCover W V v).f w ≫ V.f v = (appendCommonCover W V).f ⟨w, v⟩ :=
  (commonPolynomialChartIso_map W V v w).trans (Category.id_comp _)

private theorem polynomialFine_square {Y YK PK : Scheme.{u}}
    (W V : Y.OpenCover.{u}) (v : V.I₀) (w : W.I₀)
    (q : YK ⟶ Y) (g : PK ⟶ YK) (z : PK ⟶ V.X v)
    (hwhole : z ≫ V.f v = g ≫ q)
    {A : Scheme.{u}} (a : A ⟶ PK)
    (u : A ⟶ (commonPolynomialCover W V v).X w)
    (hsmall : u ≫ (commonPolynomialCover W V v).f w = a ≫ z) :
    u ≫ (appendCommonCover W V).f ⟨w, v⟩ = (a ≫ g) ≫ q := by
  calc
    _ = u ≫ ((commonPolynomialCover W V v).f w ≫ V.f v) :=
      congrArg (fun k => u ≫ k) (polynomialCover_map W V v w).symm
    _ = (u ≫ (commonPolynomialCover W V v).f w) ≫ V.f v :=
      (Category.assoc _ _ _).symm
    _ = (a ≫ z) ≫ V.f v := congrArg (fun k => k ≫ V.f v) hsmall
    _ = a ≫ (g ≫ q) := (Category.assoc _ _ _).trans (congrArg (fun k => a ≫ k) hwhole)
    _ = _ := (Category.assoc _ _ _).symm

private def polynomialFineCoframe {Y : Scheme.{u}} (W V : Y.OpenCover.{u})
    (v : V.I₀) (L : Y.Modules)
    (E : ∀ w : W.I₀,
      (Scheme.Modules.pullback ((appendCommonCover W V).f ⟨w, v⟩)).obj L ≅
        unitModule ((commonPolynomialCover W V v).X w)) (w : W.I₀) :
    (Scheme.Modules.pullback ((commonPolynomialCover W V v).f w)).obj
        ((Scheme.Modules.pullback (V.f v)).obj L) ≅
      unitModule ((commonPolynomialCover W V v).X w) :=
  (pullbackComp ((commonPolynomialCover W V v).f w) (V.f v)).app L ≪≫
    (pullbackCongr (polynomialCover_map W V v w)).app L ≪≫ E w

/-- The matching refinement constructs a coframe on one whole polynomial chart,
using the same line isomorphism and polynomial coframe in every scalar comparison. -/
theorem commonPolynomialCoframe_glue {R K : Type u} [CommRing R] [CommRing K]
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
    scalarCoframeCover (commonPolynomialCover W V v)
      ((Scheme.Modules.pullback (V.f v)).obj L) (polynomialFineCoframe W V v L E) := by
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
  exact scalarCoframe_glue hR (V.f v ≫ base) baseK z hfield U
    (fun w => inferInstance) A a u hchart ((Scheme.Modules.pullback (V.f v)).obj L)
    FK (polynomialFineCoframe W V v L E) hcompare

end SchubertGeometry
