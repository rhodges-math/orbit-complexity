import OrbitComplexity.SchubertGeometry.Parabolics.Stability
import OrbitComplexity.SchubertGeometry.Parabolics.CellProjection

/-! # Stabilizers under partial flag projection

An equivariant image is preserved by every element preserving its source set. Applying
this to the Schubert projection gives the inclusion between its two stabilizers.
-/

noncomputable section
namespace SchubertGeometry
open GroupActions ReductiveGroups SchubertGeometry
open scoped Pointwise

private theorem stabilizer_image {Γ X Y : Type*} [Group Γ]
    [MulAction Γ X] [MulAction Γ Y] (f : X → Y)
    (heq : ∀ g : Γ, ∀ x : X, f (g • x) = g • f x) (S : Set X) :
    MulAction.stabilizer Γ S ≤ MulAction.stabilizer Γ (f '' S) := by
  apply (MulAction.le_stabilizer_iff_smul_le (f '' S) (MulAction.stabilizer Γ S)).mpr
  intro g hg
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨g • x, ?_, heq g x⟩
  exact (MulAction.le_stabilizer_iff_smul_le S (MulAction.stabilizer Γ S)).mp
    le_rfl g hg ⟨x, hx, rfl⟩

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- Every full Schubert stabilizer preserves its image in the partial flag variety. -/
theorem schubertStabilizer_le_partial (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    schubertStabilizer G w ≤ MulAction.stabilizer G.points
      ((partialFlagPointsEquiv G J) ⁻¹'
        Set.range (Variety.mapPoints (partialSchubertInclusion G J w))) := by
  have hset : (partialFlagPointsEquiv G J) ⁻¹'
      Set.range (Variety.mapPoints (partialSchubertInclusion G J w)) =
        partialSchubertPoints G J w := partialSchubert_points G J w
  rw [hset, ← partialSchubert_image G J w hw]
  exact stabilizer_image (partialFlagProjection G J) (partialFlagProjection_smul G J) _

end SchubertGeometry
