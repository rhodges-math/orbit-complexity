import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCoordinates
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicProjection

/-!
# Root supports for the heart

The parabolic factorization partitions the inversion roots into the parabolic part
and the positive translate of the minimal representative inversion roots.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The positive roots transported from the minimal left parabolic factor. -/
def heartRootIndices (I : Set G.rootBase.support) (w : G.weylGroup) : Set G.rootIndex :=
  {r | G.rootBase.IsPos r ∧
    G.rootSystem.weylGroupToPerm (leftParabolicFactor G.rootBase I w)⁻¹ r ∈
      leftRootInversionIndices G.rootBase (leftParabolicRepresentative G.rootBase I w)}

/-- The coordinate roots of the heart form an integrally closed positive-root set. -/
theorem heartRootIndices_closed (I : Set G.rootBase.support) (w : G.weylGroup) :
    IsPositiveRootClosed G.rootBase (heartRootIndices G I w) :=
  (LeftRootInversionIndices.isPositiveRootClosed G.rootBase
    (leftParabolicRepresentative G.rootBase I w)).weyl_preimage (fun _ hi => hi.1) _

/-- The heart coordinate roots are the translated inversions of the minimal factor. -/
theorem heartRootIndices_eq_image (I : Set G.rootBase.support) (w : G.weylGroup) :
    heartRootIndices G I w =
      G.rootSystem.weylGroupToPerm (leftParabolicFactor G.rootBase I w) ''
        leftRootInversionIndices G.rootBase (leftParabolicRepresentative G.rootBase I w) := by
  let a := leftParabolicFactor G.rootBase I w
  let d := leftParabolicRepresentative G.rootBase I w
  have hadd : rootInversionCount G.rootBase (a * d) =
      rootInversionCount G.rootBase a + rootInversionCount G.rootBase d :=
    RootInversionCount.mul_parabolic_of_minimal_left G.rootBase I a d
      (leftParabolicRepresentative_minimal G.rootBase I w) (leftParabolicFactor_mem _ _ _)
  ext r
  constructor
  · rintro ⟨_, hr⟩
    refine ⟨G.rootSystem.weylGroupToPerm a⁻¹ r, hr, ?_⟩
    change G.rootSystem.weylGroupToPerm a (G.rootSystem.weylGroupToPerm a⁻¹ r) = r
    simp only [map_inv, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨weyl_image_inversions_isPos_of_count_add G.rootBase a d hadd hs, ?_⟩
    simpa only [map_inv, Equiv.Perm.coe_inv, Equiv.symm_apply_apply] using hs

/-- The parabolic and heart coordinate roots partition the inversion roots of the product. -/
theorem inversionRoots_eq_union_heart (I : Set G.rootBase.support) (w : G.weylGroup) :
    leftRootInversionIndices G.rootBase w =
      leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) ∪
        heartRootIndices G I w := by
  let a := leftParabolicFactor G.rootBase I w
  let d := leftParabolicRepresentative G.rootBase I w
  have hv := LeftRootInversions.leftParabolic_decomposition G.rootBase I w
  ext i
  constructor
  · intro hi
    have hm : G.rootSystem.root i ∈ leftRootInversions G.rootBase w :=
      (root_mem_leftRootInversions G.rootBase w i).mpr hi
    rw [hv] at hm
    rcases hm with ha | hd
    · exact Or.inl ((root_mem_leftRootInversions G.rootBase a i).mp ha)
    · obtain ⟨_, ⟨j, hj, rfl⟩, he⟩ := hd
      right
      rw [heartRootIndices_eq_image]
      exact ⟨j, hj, G.rootSystem.root.injective
        ((G.rootSystem.weylGroup_apply_root a j).symm.trans he)⟩
  · rintro (ha | hd)
    · apply (root_mem_leftRootInversions G.rootBase w i).mp
      rw [hv]
      exact Or.inl ((root_mem_leftRootInversions G.rootBase a i).mpr ha)
    · rw [heartRootIndices_eq_image] at hd
      obtain ⟨j, hj, he⟩ := hd
      apply (root_mem_leftRootInversions G.rootBase w i).mp
      rw [hv]
      exact Or.inr ⟨G.rootSystem.root j, ⟨j, hj, rfl⟩,
        (G.rootSystem.weylGroup_apply_root a j).trans (congrArg G.rootSystem.root he)⟩

/-- The parabolic inversion roots and the heart coordinate roots are disjoint. -/
theorem inversionRoots_disjoint_heart (I : Set G.rootBase.support) (w : G.weylGroup) :
    Disjoint (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
      (heartRootIndices G I w) := by
  rw [Set.disjoint_left]
  intro i hi hh
  rw [heartRootIndices_eq_image] at hh
  obtain ⟨j, hj, he⟩ := hh
  apply Set.disjoint_left.mp (leftRootInversions_disjoint_weyl_image G.rootBase
    (leftParabolicFactor G.rootBase I w) (leftParabolicRepresentative G.rootBase I w))
    (⟨i, hi, rfl⟩ : G.rootSystem.root i ∈ leftRootInversions G.rootBase _)
  exact ⟨G.rootSystem.root j, ⟨j, hj, rfl⟩,
    (G.rootSystem.weylGroup_apply_root _ j).trans (congrArg G.rootSystem.root he)⟩

end SchubertOrbits
