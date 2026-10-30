import OrbitComplexity.Paper.Heart.RootSets
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTransport
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTorus
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootProducts

/-!
# The conjugated subgroup in the heart decomposition

The subgroup V_d is the Weyl conjugate aU_da⁻¹. Its root support is the
translated inversion support in the heart decomposition. This identifies its
normalization by the torus and the unique products with U_a in both orders.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace SchubertOrbits.Vd
open ReductiveGroups TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The subgroup V_d=aU_da⁻¹ for the left parabolic decomposition w=ad. -/
def points (I : Set G.rootBase.support) (w : G.weylGroup) : Subgroup G.points :=
  (G.rootSubsetPoints
    (leftRootInversionIndices G.rootBase (leftParabolicRepresentative G.rootBase I w))
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)).map
      (MulAut.conj (G.weylPoint (leftParabolicFactor G.rootBase I w))).toMonoidHom

/-- The conjugated subgroup V_d is the closed subgroup with the heart root support. -/
theorem points_eq_rootSubset (I : Set G.rootBase.support) (w : G.weylGroup) :
    points G I w = G.rootSubsetPoints (heartRootIndices G I w)
      (heartRootIndices_closed G I w) := by
  apply G.rootSubsetPoints_weyl_eq
  · intro r hr
    exact (mem_leftRootInversionIndices G.rootBase _ r).mp hr |>.1
  · intro r hr
    exact hr.1
  · exact heartRootIndices_eq_image G I w

/-- The conjugated minimal-factor subgroup lies in the inversion-root subgroup of w. -/
theorem points_le_inversions (I : Set G.rootBase.support) (w : G.weylGroup) :
    points G I w ≤ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) := by
  rw [points_eq_rootSubset]
  apply G.rootSubsetPoints_mono
  intro r hr
  rw [inversionRoots_eq_union_heart G I w]
  exact Or.inr hr

/-- The maximal torus normalizes the conjugated minimal-factor subgroup. -/
theorem torus_le_normalizer (I : Set G.rootBase.support) (w : G.weylGroup) :
    G.torusPoints ≤ Subgroup.normalizer (points G I w : Set G.points) := by
  rw [points_eq_rootSubset]
  exact G.torusPoints_le_rootNormalizer _ _

/-- The parabolic inversion subgroup and V_d multiply with unique factors to U_w. -/
theorem existsUnique_mul (I : Set G.rootBase.support) (w : G.weylGroup)
    (g : G.points) (hg : g ∈ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)) :
    ∃! p : G.points × G.points,
      p.1 ∈ G.rootSubsetPoints
        (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) ∧
      p.2 ∈ points G I w ∧ p.1 * p.2 = g := by
  rw [points_eq_rootSubset]
  exact G.rootSubsetPoints_existsUnique_mul _ _ _
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)
    (heartRootIndices_closed G I w) (inversionRoots_eq_union_heart G I w)
    (inversionRoots_disjoint_heart G I w) g hg

/-- Reversing the two factors still gives unique multiplication factors in U_w. -/
theorem existsUnique_mul_rev (I : Set G.rootBase.support) (w : G.weylGroup)
    (g : G.points) (hg : g ∈ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)) :
    ∃! p : G.points × G.points,
      p.1 ∈ points G I w ∧
      p.2 ∈ G.rootSubsetPoints
        (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) ∧ p.1 * p.2 = g := by
  rw [points_eq_rootSubset]
  exact G.rootSubsetPoints_existsUnique_mul _ _ _
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
    (heartRootIndices_closed G I w)
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)
    ((inversionRoots_eq_union_heart G I w).trans (Set.union_comm _ _))
    (inversionRoots_disjoint_heart G I w).symm g hg

end SchubertOrbits.Vd
