import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingCover
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.ScalarOverlapSquares
import Batteries.Tactic.Lint

/-! # Scalar comparison of common covers

Cartesian comparisons for the two chart families induce a Cartesian
comparison for their common cover. The induced map preserves both chart
projections and the structure map to the coefficient spectrum.
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting

namespace SchubertGeometry

variable {Y YT : Scheme.{u}} (q : YT ⟶ Y)
  (W V : Y.OpenCover.{u}) (WT VT : YT.OpenCover.{u})
  (σ : WT.I₀ → W.I₀) (τ : VT.I₀ → V.I₀)
  (u : ∀ i, WT.X i ⟶ W.X (σ i)) (v : ∀ i, VT.X i ⟶ V.X (τ i))
  (hu : ∀ i, u i ≫ W.f (σ i) = WT.f i ≫ q)
  (hv : ∀ i, v i ≫ V.f (τ i) = VT.f i ≫ q)

/-- The common-cover chart map induced by the two scalar chart maps. -/
def scalarCommonMap (l : (appendCommonCover WT VT).I₀) :
    (appendCommonCover WT VT).X l ⟶
      (appendCommonCover W V).X ⟨σ l.1, τ l.2⟩ :=
  pullback.map (WT.f l.1) (VT.f l.2) (W.f (σ l.1)) (V.f (τ l.2))
    (u l.1) (v l.2) q (hu l.1).symm (hv l.2).symm

/-- The induced common-cover map preserves its first projection. -/
theorem scalarCommonMap_left (l : (appendCommonCover WT VT).I₀) :
    scalarCommonMap q W V WT VT σ τ u v hu hv l ≫
      appendCommonLeft W V ⟨σ l.1, τ l.2⟩ =
      appendCommonLeft WT VT l ≫ u l.1 := by
  exact pullback.lift_fst _ _ _

/-- The induced common-cover map preserves its second projection. -/
theorem scalarCommonMap_right (l : (appendCommonCover WT VT).I₀) :
    scalarCommonMap q W V WT VT σ τ u v hu hv l ≫
      appendCommonRight W V ⟨σ l.1, τ l.2⟩ =
      appendCommonRight WT VT l ≫ v l.2 := by
  exact pullback.lift_snd _ _ _

/-- Cartesian scalar squares for both chart families give a Cartesian
square for each common-cover chart. -/
theorem scalarCommonMap_isPullback
    (hU : ∀ i, IsPullback (u i) (WT.f i) (W.f (σ i)) q)
    (hV : ∀ i, IsPullback (v i) (VT.f i) (V.f (τ i)) q)
    (l : (appendCommonCover WT VT).I₀) :
    IsPullback (scalarCommonMap q W V WT VT σ τ u v hu hv l)
      ((appendCommonCover WT VT).f l)
      ((appendCommonCover W V).f ⟨σ l.1, τ l.2⟩) q :=
  scalarOverlap_isPullback (W.f (σ l.1)) (V.f (τ l.2))
    (WT.f l.1) (VT.f l.2) (u l.1) (v l.2) q (hu l.1) (hv l.2)
    (W.f (σ l.1)) (WT.f l.1) q (hU l.1) (hV l.2)

/-- The common-cover comparison is Cartesian over the coefficient spectra
and retains the structure maps of the same two models. -/
theorem scalarCommonMap_base {B BT : Scheme.{u}}
    (base : Y ⟶ B) (baseT : YT ⟶ BT) (β : BT ⟶ B)
    (hq : IsPullback q baseT base β)
    (hU : ∀ i, IsPullback (u i) (WT.f i) (W.f (σ i)) q)
    (hV : ∀ i, IsPullback (v i) (VT.f i) (V.f (τ i)) q)
    (l : (appendCommonCover WT VT).I₀) :
    IsPullback (scalarCommonMap q W V WT VT σ τ u v hu hv l)
      ((appendCommonCover WT VT).f l ≫ baseT)
      ((appendCommonCover W V).f ⟨σ l.1, τ l.2⟩ ≫ base) β :=
  (scalarCommonMap_isPullback q W V WT VT σ τ u v hu hv hU hV l).paste_vert hq

end SchubertGeometry
