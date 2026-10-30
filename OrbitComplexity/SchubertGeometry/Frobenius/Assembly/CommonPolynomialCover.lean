import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingCover
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The matching cover on a fixed polynomial chart

Pulling the matching cover to one polynomial chart gives an open cover
whose schemes are the corresponding schemes in the common refinement.
The chosen order of the pullback factors preserves both projections.
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SchubertGeometry

open private affine_fibre_product from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameCoverRefinement

/-- The matching cover pulled back to one prescribed polynomial chart. -/
def commonPolynomialCover {Y : Scheme.{u}} (W V : Y.OpenCover.{u}) (v : V.I₀) :
    (V.X v).OpenCover.{u} :=
  W.pullback₂ (V.f v)

/-- Pulling back a finite matching cover gives finitely many charts. -/
instance {Y : Scheme.{u}} (W V : Y.OpenCover.{u}) (v : V.I₀) [Finite W.I₀] :
    Finite (commonPolynomialCover W V v).I₀ :=
  inferInstanceAs (Finite W.I₀)

/-- The pulled-back charts are affine over a separated scheme. -/
instance {Y : Scheme.{u}} [Y.IsSeparated] (W V : Y.OpenCover.{u})
    [∀ w, IsAffine (W.X w)] [∀ v, IsAffine (V.X v)]
    (v : V.I₀) (w : (commonPolynomialCover W V v).I₀) :
    IsAffine ((commonPolynomialCover W V v).X w) := by
  let : IsAffine (W.X w) := (inferInstance : ∀ j, IsAffine (W.X j)) w
  let : IsAffine (V.X v) := (inferInstance : ∀ j, IsAffine (V.X j)) v
  exact affine_fibre_product (W.f w) (V.f v)

/-- The fixed polynomial cover uses the same scheme as the corresponding
member of the common refinement. -/
def commonPolynomialChartIso {Y : Scheme.{u}} (W V : Y.OpenCover.{u})
    (v : V.I₀) (w : (commonPolynomialCover W V v).I₀) :
    (commonPolynomialCover W V v).X w ≅ (appendCommonCover W V).X ⟨w, v⟩ :=
  Iso.refl _

/-- The matching projection is preserved by the chart identification. -/
theorem commonPolynomialChartIso_left {Y : Scheme.{u}} (W V : Y.OpenCover.{u})
    (v : V.I₀) (w : (commonPolynomialCover W V v).I₀) :
    (commonPolynomialChartIso W V v w).hom ≫ appendCommonLeft W V ⟨w, v⟩ =
      pullback.fst (W.f w) (V.f v) :=
  Category.id_comp _

/-- The polynomial projection is the map in the fixed polynomial cover. -/
theorem commonPolynomialChartIso_right {Y : Scheme.{u}} (W V : Y.OpenCover.{u})
    (v : V.I₀) (w : (commonPolynomialCover W V v).I₀) :
    (commonPolynomialChartIso W V v w).hom ≫ appendCommonRight W V ⟨w, v⟩ =
      (commonPolynomialCover W V v).f w :=
  Category.id_comp _

/-- The fixed polynomial cover retains the prescribed map to the global model. -/
theorem commonPolynomialChartIso_map {Y : Scheme.{u}} (W V : Y.OpenCover.{u})
    (v : V.I₀) (w : (commonPolynomialCover W V v).I₀) :
    (commonPolynomialCover W V v).f w ≫ V.f v =
      (commonPolynomialChartIso W V v w).hom ≫ (appendCommonCover W V).f ⟨w, v⟩ := by
  change pullback.snd (W.f w) (V.f v) ≫ V.f v =
    𝟙 _ ≫ (pullback.fst (W.f w) (V.f v) ≫ W.f w)
  exact (pullback.condition (f := W.f w) (g := V.f v)).symm.trans
    (Category.id_comp _).symm

/-- The cover chart and its two prescribed projections form a pullback square. -/
theorem commonPolynomialCover_isPullback {Y : Scheme.{u}} (W V : Y.OpenCover.{u})
    (v : V.I₀) (w : (commonPolynomialCover W V v).I₀) :
    IsPullback (pullback.fst (W.f w) (V.f v))
      ((commonPolynomialCover W V v).f w) (W.f w) (V.f v) :=
  IsPullback.of_hasPullback (W.f w) (V.f v)

end SchubertGeometry
