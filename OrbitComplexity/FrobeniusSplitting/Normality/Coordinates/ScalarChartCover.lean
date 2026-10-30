import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Batteries.Tactic.Lint

/-!
# Covers from prescribed Cartesian charts

A cover pulls back to any family of schemes with the prescribed Cartesian
squares. Its chart schemes and arrows remain the given ones.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FrobeniusSplitting

/-- The scalar cover with prescribed Cartesian chart schemes and arrows. -/
def scalarChartCover {Y Z : Scheme.{u}} (q : Z ⟶ Y) (U : Scheme.OpenCover.{u} Y)
    (P : U.I₀ → Scheme.{u}) (j : ∀ i, P i ⟶ Z) (k : ∀ i, P i ⟶ U.X i)
    (h : ∀ i, IsPullback (k i) (j i) (U.f i) q) : Scheme.OpenCover.{u} Z :=
  Scheme.Cover.copy (U.pullback₂ q) U.I₀ P j (Equiv.refl _) (fun i => (h i).isoPullback)
    (fun i => (h i).isoPullback_hom_snd.symm)

/-- The scalar cover retains the prescribed chart scheme. -/
theorem scalarChartCover_obj {Y Z : Scheme.{u}} (q : Z ⟶ Y)
    (U : Scheme.OpenCover.{u} Y) (P : U.I₀ → Scheme.{u})
    (j : ∀ i, P i ⟶ Z) (k : ∀ i, P i ⟶ U.X i)
    (h : ∀ i, IsPullback (k i) (j i) (U.f i) q) (i : U.I₀) :
    (scalarChartCover q U P j k h).X i = P i := rfl

/-- The scalar cover retains the prescribed chart arrow. -/
theorem scalarChartCover_map {Y Z : Scheme.{u}} (q : Z ⟶ Y)
    (U : Scheme.OpenCover.{u} Y) (P : U.I₀ → Scheme.{u})
    (j : ∀ i, P i ⟶ Z) (k : ∀ i, P i ⟶ U.X i)
    (h : ∀ i, IsPullback (k i) (j i) (U.f i) q) (i : U.I₀) :
    (scalarChartCover q U P j k h).f i = j i := rfl

/-- The prescribed Cartesian chart arrow is an open immersion. -/
theorem scalarChartCover_isOpen {Y Z : Scheme.{u}} (q : Z ⟶ Y)
    (U : Scheme.OpenCover.{u} Y) (P : U.I₀ → Scheme.{u})
    (j : ∀ i, P i ⟶ Z) (k : ∀ i, P i ⟶ U.X i)
    (h : ∀ i, IsPullback (k i) (j i) (U.f i) q) (i : U.I₀) :
    IsOpenImmersion (j i) :=
  (scalarChartCover q U P j k h).map_prop i

/-- A finite cover has a finite prescribed scalar cover. -/
instance {Y Z : Scheme.{u}} (q : Z ⟶ Y) (U : Scheme.OpenCover.{u} Y)
    [Finite U.I₀] (P : U.I₀ → Scheme.{u}) (j : ∀ i, P i ⟶ Z)
    (k : ∀ i, P i ⟶ U.X i)
    (h : ∀ i, IsPullback (k i) (j i) (U.f i) q) :
    Finite (scalarChartCover q U P j k h).I₀ :=
  inferInstanceAs (Finite U.I₀)

end FrobeniusSplitting
