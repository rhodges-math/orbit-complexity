import OrbitComplexity.Paper.Heart.TrivialComplement
import OrbitComplexity.SchubertGeometry.Parabolics.LeviStability
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.Longest

/-! # Equivalent parabolic stability conditions

The complementary unipotent group is trivial precisely when the parabolic factor
is longest, or equivalently when the standard Levi acts on the Schubert variety.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups SchubertGeometry GroupActions CategoryTheory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem complementRootIndices_eq (I : Set G.rootBase.support) (w : G.weylGroup) :
    complementRootIndices G I w = leviPositiveRoots G.rootBase I \
      leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) := by
  ext r
  simp only [complementRootIndices, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_sdiff]
  exact and_congr_right fun hr =>
    and_iff_right hr.1

private theorem leftDescent_iff (w : G.weylGroup) (i : G.rootBase.support) :
    (weylCoxeterSystem G.rootBase).IsLeftDescent w i ↔
      ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i.val) := by
  rw [← (weylCoxeterSystem G.rootBase).isRightDescent_inv_iff]
  simp only [CoxeterSystem.IsRightDescent, weylCoxeterSystem_simple, weylCoxeterSystem_length]
  by_cases hp : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i.val)
  · rw [rootInversionCount_mul_simple_of_pos G.rootBase w⁻¹ i hp]
    constructor
    · intro h
      omega
    · intro hn
      exact (hn hp).elim
  · have hdrop := rootInversionCount_mul_simple_of_neg G.rootBase w⁻¹ i
      ((root_height_neg_iff_not_isPos G.rootBase _).mpr hp)
    constructor
    · exact fun _ => hp
    · intro _
      omega

/-- Trivial complement, empty support, a Levi action, left descents and the longest factor agree. -/
theorem complement_equivalences (I : Set G.rootBase.support) (w : G.weylGroup) :
    (G.rootSubsetPoints (complementRootIndices G I w) (complementRootIndices_closed G I w) = ⊥ ↔
      leviPositiveRoots G.rootBase I \
        leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) = ∅) ∧
    ((leviPositiveRoots G.rootBase I \
        leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) = ∅) ↔
      ∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
        letI := a
        IsModHom (leviVariety G I).toOver (schubertInclusion G w)) ∧
    ((∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
        letI := a
        IsModHom (leviVariety G I).toOver (schubertInclusion G w)) ↔
      I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w) ∧
    ((I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w) ↔
      leftParabolicFactor G.rootBase I w = longestParabolicElement G.rootBase I) := by
  have hdes : (I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w) ↔
      ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i) := by
    constructor
    · exact fun h i hi => (leftDescent_iff G w i).mp (h hi)
    · exact fun h i hi => (leftDescent_iff G w i).mpr (h i hi)
  have hl := leftFactor_longest_iff G.rootBase I w
  have ht : (G.rootSubsetPoints (complementRootIndices G I w)
      (complementRootIndices_closed G I w) = ⊥) ↔
      leviPositiveRoots G.rootBase I \
        leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) = ∅ := by
    rw [← complementRootIndices_eq]
    exact complement_trivial_iff G I w
  exact ⟨ht, hl.1.symm.trans (hl.2.trans
    (hdes.symm.trans (levi_schubert_action_iff G I w).symm)),
    levi_schubert_action_iff G I w, hdes.trans hl.2.symm⟩

/-- The five equivalent parabolic stability conditions over the complex numbers. -/
theorem complement_equivalences_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup) :
    (G.rootSubsetPoints (complementRootIndices G I w) (complementRootIndices_closed G I w) = ⊥ ↔
      leviPositiveRoots G.rootBase I \
        leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) = ∅) ∧
    ((leviPositiveRoots G.rootBase I \
        leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) = ∅) ↔
      ∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
        letI := a
        IsModHom (leviVariety G I).toOver (schubertInclusion G w)) ∧
    ((∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
        letI := a
        IsModHom (leviVariety G I).toOver (schubertInclusion G w)) ↔
      I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w) ∧
    ((I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w) ↔
      leftParabolicFactor G.rootBase I w = longestParabolicElement G.rootBase I) :=
  complement_equivalences G I w

end SchubertOrbits
