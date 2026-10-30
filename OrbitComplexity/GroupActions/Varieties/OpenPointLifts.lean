import OrbitComplexity.GroupActions.Varieties.OpenPoints

/-!
# Lifting morphisms into open charts from rational points

For a variety over an algebraically closed field, rational points detect containment in
an open subvariety. A morphism with rational image in an open chart consequently lifts
to that chart as a morphism over the base field.

## Main results

* `GroupActions.Variety.range_subset_open_of_points`: rational detection of open containment.
* `GroupActions.Variety.liftOpen`: the lift to an open chart.
* `GroupActions.Variety.liftOpen_comp`: the factorization identity.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y Z : GroupActions.Variety K}

/-- Rational points detect containment of a morphism's image in an open subvariety. -/
theorem range_subset_open_of_points (f : X.toOver ⟶ Y.toOver) (U : Y.scheme.Opens)
    (h : ∀ p : X.points, Y.pointMap (mapPoints f p) ∈ U) :
    Set.range (f.left : X.scheme → Y.scheme) ⊆ (U : Set Y.scheme) := by
  have : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  have : JacobsonSpace X.toOver.left := inferInstanceAs (JacobsonSpace X.scheme)
  rintro _ ⟨x, rfl⟩
  by_contra hx
  have hF : IsClosed (f.left ⁻¹' (U : Set Y.scheme)ᶜ) :=
    U.isOpen.isClosed_compl.preimage f.left.continuous
  obtain ⟨z, hz, hclosed⟩ := nonempty_inter_closedPoints
    (⟨x, hx⟩ : (f.left ⁻¹' (U : Set Y.scheme)ᶜ).Nonempty) hF.isLocallyClosed
  obtain ⟨p, hp⟩ := X.pointsEquivClosedPoints.surjective ⟨z, hclosed⟩
  have hpoint := h p
  rw [pointMap_mapPoints, show X.pointMap p = z from congrArg Subtype.val hp] at hpoint
  exact hz hpoint

private theorem openRangeSubset (f : X.toOver ⟶ Y.toOver) (j : Z.toOver ⟶ Y.toOver)
    [IsOpenImmersion j.left] (h : ∀ p : X.points, mapPoints f p ∈ Set.range (mapPoints j)) :
    Set.range (f.left : X.scheme → Y.scheme) ⊆ Set.range (j.left : Z.scheme → Y.scheme) := by
  apply range_subset_open_of_points f j.left.opensRange
  intro p
  obtain ⟨q, hq⟩ := h p
  exact ⟨Z.pointMap q, congrArg Y.pointMap hq⟩

/-- A morphism whose rational points lie in an open chart lifts to that chart. -/
def liftOpen (f : X.toOver ⟶ Y.toOver) (j : Z.toOver ⟶ Y.toOver)
    [IsOpenImmersion j.left] (h : ∀ p : X.points, mapPoints f p ∈ Set.range (mapPoints j)) :
    X.toOver ⟶ Z.toOver :=
  Over.homMk (IsOpenImmersion.lift j.left f.left (openRangeSubset f j h)) (by
    rw [← j.w, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact f.w)

/-- Composing the open-chart lift with the chart inclusion recovers the morphism. -/
theorem liftOpen_comp (f : X.toOver ⟶ Y.toOver) (j : Z.toOver ⟶ Y.toOver)
    [IsOpenImmersion j.left] (h : ∀ p : X.points, mapPoints f p ∈ Set.range (mapPoints j)) :
    liftOpen f j h ≫ j = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac j.left f.left (openRangeSubset f j h)

end

end GroupActions.Variety
