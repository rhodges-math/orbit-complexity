import OrbitComplexity.GroupActions.Actions.Stabilizers

/-! # Rational points of stabilizer inclusions

The reduced stabilizer variety embeds in the acting group with rational-point image equal
to the stabilizer subgroup of the chosen point.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]

/-- The rational image of the stabilizer inclusion is exactly the stabilizer subgroup. -/
theorem stabilizerInclusion_points_range (x : X.points) :
    Set.range (Variety.mapPoints (stabilizerInclusion H X x)) =
      (MulAction.stabilizer H.points x : Set H.points) := by
  ext h
  constructor
  · rintro ⟨p, rfl⟩
    exact (stabilizerPointsEquiv H X x p).property
  · intro hh
    refine ⟨(stabilizerPointsEquiv H X x).symm ⟨h, hh⟩, ?_⟩
    exact congrArg Subtype.val ((stabilizerPointsEquiv H X x).apply_symm_apply ⟨h, hh⟩)

end

end GroupActions
