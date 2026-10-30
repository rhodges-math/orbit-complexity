import OrbitComplexity.SchubertGeometry.Parabolics.PartialFlag
import OrbitComplexity.SchubertGeometry.Parabolics.FlagDescent
import OrbitComplexity.SchubertGeometry.FlagVariety.Action
import OrbitComplexity.GroupActions.Actions.EquivariantPoints

/-! # Projection from complete to partial flags

The group orbit morphism descends uniquely through the Borel quotient. Its descended
morphism is surjective and equivariant, and on rational points it is the standard
projection of Borel cosets to parabolic cosets.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem rightInvariant (J : Set G.rootBase.support)
    (g : G.points) (b : G.borelPoints) :
    Variety.mapPoints (partialFlagQuotient G J) (reductivePointsMulEquiv G (g * b)) =
      Variety.mapPoints (partialFlagQuotient G J) (reductivePointsMulEquiv G g) := by
  rw [partialFlagQuotient_points, partialFlagQuotient_points]
  apply congrArg (partialFlagPointsEquiv G J)
  symm
  apply QuotientGroup.eq.mpr
  have hb : b.val ∈ standardParabolicPoints G J :=
    (show G.borelPoints ≤ standardParabolicPoints G J from le_sup_left) b.property
  simpa only [inv_mul_cancel_left] using hb

private theorem projection_exists (J : Set G.rootBase.support) :
    ∃! π : (flagVariety G).toOver ⟶ (partialFlagVariety G J).toOver,
      flagQuotientMorphism G ≫ π = partialFlagQuotient G J :=
  flagQuotient_desc G (partialFlagVariety G J) (partialFlagQuotient G J)
    (rightInvariant G J)

/-- The regular projection from complete flags to standard partial flags. -/
def partialFlagMorphism (J : Set G.rootBase.support) :
    (flagVariety G).toOver ⟶ (partialFlagVariety G J).toOver :=
  Classical.choose (projection_exists G J)

/-- The complete-to-partial projection factors the group orbit morphism. -/
theorem partialFlagMorphism_quotient (J : Set G.rootBase.support) :
    flagQuotientMorphism G ≫ partialFlagMorphism G J = partialFlagQuotient G J :=
  (Classical.choose_spec (projection_exists G J)).1

/-- The complete-to-partial flag projection is surjective on scheme points. -/
instance partialFlagMorphism_surjective (J : Set G.rootBase.support) :
    Surjective (partialFlagMorphism G J).left := by
  have hsurj : Surjective ((flagQuotientMorphism G).left ≫
      (partialFlagMorphism G J).left) := by
    change Surjective ((flagQuotientMorphism G ≫ partialFlagMorphism G J).left)
    rw [partialFlagMorphism_quotient]
    infer_instance
  exact Surjective.of_comp (flagQuotientMorphism G).left (partialFlagMorphism G J).left

/-- The flag projection induces the standard projection of rational cosets. -/
theorem partialFlagMorphism_points (J : Set G.rootBase.support) (p : flagPoints G) :
    Variety.mapPoints (partialFlagMorphism G J) (flagVarietyPointsEquiv G p) =
      partialFlagPointsEquiv G J (partialFlagProjection G J p) := by
  obtain ⟨g, rfl⟩ := flagProjection_surjective G p
  have hB : Variety.mapPoints (flagQuotientMorphism G) (reductivePointsMulEquiv G g) =
      flagVarietyPointsEquiv G (flagProjection G g) := flagQuotientMorphism_points G g
  have hc := congrArg (fun f => Variety.mapPoints f (reductivePointsMulEquiv G g))
    (partialFlagMorphism_quotient G J)
  rw [Variety.mapPoints_comp, hB, partialFlagQuotient_points] at hc
  exact hc

/-- The complete-to-partial flag projection is equivariant for left multiplication. -/
theorem partialFlagMorphism_isModHom (J : Set G.rootBase.support) :
    IsModHom (reductiveVariety G).toOver (partialFlagMorphism G J) := by
  apply Variety.isModHom_of_points (reductiveVariety G) (flagVariety G)
    (partialFlagVariety G J) (partialFlagMorphism G J)
  intro h x
  obtain ⟨g, rfl⟩ := (reductivePointsMulEquiv G).surjective h
  obtain ⟨p, rfl⟩ := (flagVarietyPointsEquiv G).surjective x
  rw [flagVarietyAction_points, partialFlagMorphism_points, partialFlagProjection_smul,
    ← partialFlag_smul, partialFlagMorphism_points]

end SchubertGeometry
