import Mathlib.AlgebraicGeometry.Gluing

/-! # Rational points in glued affine charts

Every point over a field factors through a member of an open cover.
Applied to scheme gluing, this gives a section in one of the charts representing any
rational point of the glued scheme.

## Main results

* `GroupActions.point_factors_openCover`: field points lift to open charts.
* `GroupActions.point_factors_glued`: sections of a glued scheme lift to its charts.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

universe u v

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- A morphism from the spectrum of a field factors through an open chart. -/
theorem point_factors_openCover (cover : Scheme.OpenCover.{v} X)
    (point : Spec (CommRingCat.of K) ⟶ X) :
    ∃ (i : cover.I₀) (lift : Spec (CommRingCat.of K) ⟶ cover.X i),
      lift ≫ cover.f i = point := by
  obtain ⟨i, y, hy⟩ := cover.exists_eq (point (IsLocalRing.closedPoint K))
  have hrange : Set.range point ⊆ Set.range (cover.f i) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨y, ?_⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
    exact hy
  exact ⟨i, IsOpenImmersion.lift (cover.f i) point hrange,
    IsOpenImmersion.lift_fac (cover.f i) point hrange⟩

/-- A rational section of a glued scheme is represented by a rational section of a chart. -/
theorem point_factors_glued (data : Scheme.GlueData.{u})
    (toSpec : data.glued ⟶ Spec (CommRingCat.of K))
    (point : {p : Spec (CommRingCat.of K) ⟶ data.glued // p ≫ toSpec = 𝟙 _}) :
    ∃ (i : data.J)
      (lift : {p : Spec (CommRingCat.of K) ⟶ data.U i //
        p ≫ data.ι i ≫ toSpec = 𝟙 _}), lift.val ≫ data.ι i = point.val := by
  change ∃ (i : data.openCover.I₀)
    (lift : {p : Spec (CommRingCat.of K) ⟶ data.openCover.X i //
      p ≫ data.openCover.f i ≫ toSpec = 𝟙 _}),
    lift.val ≫ data.openCover.f i = point.val
  obtain ⟨i, lift, hlift⟩ := point_factors_openCover data.openCover point.val
  refine ⟨i, ⟨lift, ?_⟩, hlift⟩
  simpa only [Category.assoc] using
    (congrArg (fun morphism => morphism ≫ toSpec) hlift).trans point.property

end GroupActions