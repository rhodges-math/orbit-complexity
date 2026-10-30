import OrbitComplexity.GroupActions.Varieties.Morphisms
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Fibres over rational points

A rational point of a separated variety is a closed immersion. Its pullback
has the same underlying fibre, and therefore the same dimension, as the
scheme-theoretic fibre at the corresponding point.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] {X Y : GroupActions.Variety K}

/-- A rational point of a variety is a closed immersion of schemes. -/
instance point_isClosedImmersion (x : X.points) : IsClosedImmersion x.val := by
  have : IsClosedImmersion (x.val ≫ X.toSpec) := by
    rw [x.property]
    infer_instance
  exact IsClosedImmersion.of_comp x.val X.toSpec

private lemma point_range (x : X.points) : Set.range x.val = {X.pointMap x} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact congrArg x.val (Subsingleton.elim z (IsLocalRing.closedPoint K))
  · rintro rfl
    exact ⟨IsLocalRing.closedPoint K, rfl⟩

/-- Pullback over a rational point is homeomorphic to the corresponding
scheme-theoretic fibre. -/
def pointPullbackHomeomorph (f : Y.toOver ⟶ X.toOver) (x : X.points) :
    (pullback f.left x.val : Scheme) ≃ₜ f.left.fiber (X.pointMap x) :=
  (pullback.fst f.left x.val).isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr (by rw [Scheme.Pullback.range_fst, point_range])).trans
      (f.left.fiberHomeo (X.pointMap x)).symm)

/-- The fibre comparison preserves the underlying point of the source variety. -/
theorem pointPullbackHomeomorph_fst (f : Y.toOver ⟶ X.toOver) (x : X.points)
    (z : (pullback f.left x.val : Scheme)) :
    f.left.fiberι (X.pointMap x) (pointPullbackHomeomorph f x z) =
      pullback.fst f.left x.val z :=
  f.left.fiberι_fiberHomeo_symm _ _

end

end GroupActions.Variety
