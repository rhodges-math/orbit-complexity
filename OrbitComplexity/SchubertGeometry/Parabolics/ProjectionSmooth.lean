import OrbitComplexity.SchubertGeometry.Parabolics.Proper
import OrbitComplexity.GroupActions.Actions.HomogeneousSmooth

/-! # Smooth parabolic projection

The projection from complete to partial flags is smooth by equivariance and transitivity.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The standard partial flag variety is integral. -/
instance partialFlagVarietyIntegral (J : Set G.rootBase.support) :
    IsIntegral (partialFlagVariety G J).scheme := by
  unfold partialFlagVariety
  infer_instance

private theorem flagTrans (a b : (flagVariety G).points) :
    ∃ h : (reductiveVariety G).points, h • a = b := by
  obtain ⟨qa, rfl⟩ := (flagVarietyPointsEquiv G).surjective a
  obtain ⟨qb, rfl⟩ := (flagVarietyPointsEquiv G).surjective b
  obtain ⟨ga, rfl⟩ := flagProjection_surjective G qa
  obtain ⟨gb, rfl⟩ := flagProjection_surjective G qb
  refine ⟨reductivePointsMulEquiv G (gb * ga⁻¹), ?_⟩
  rw [flagVarietyAction_points]
  apply congrArg (flagVarietyPointsEquiv G)
  change QuotientGroup.mk ((gb * ga⁻¹) * ga) = QuotientGroup.mk gb
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- The projection from complete to partial flags is smooth. -/
theorem partialFlagMorphism_smooth (J : Set G.rootBase.support) :
    Smooth (partialFlagMorphism G J).left := by
  let : IsModHom (reductiveVariety G).toOver (partialFlagMorphism G J) :=
    partialFlagMorphism_isModHom G J
  have : IsDominant (partialFlagMorphism G J).left := inferInstance
  exact smooth_of_transitive (reductiveVariety G) (flagVariety G)
    (partialFlagVariety G J) (partialFlagMorphism G J) (flagTrans G)

end SchubertGeometry
