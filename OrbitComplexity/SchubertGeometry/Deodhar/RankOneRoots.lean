import OrbitComplexity.SchubertGeometry.Cells.RootChart
import OrbitComplexity.ReductiveGroups.Roots.Inversions.ClosedRootTransport

/-! # Root supports in a rank-one cell extension

Appending an increasing simple reflection adds a disjoint closed singleton root support.
-/

open ReductiveGroups
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)

/-- The root direction added by right multiplication by a simple reflection. -/
abbrev rankOneRootSet : Set G.rootIndex := {G.rootSystem.weylGroupToPerm w i}

/-- A positive Weyl translate of a simple root is a closed root support. -/
theorem rankOneRoot_closed (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i)) :
    IsPositiveRootClosed G.rootBase (rankOneRootSet G w i) := by
  have hs : IsPositiveRootClosed G.rootBase {(i : G.rootIndex)} := by
    rw [← leftRootInversionIndices_simple G.rootBase i]
    exact LeftRootInversionIndices.isPositiveRootClosed G.rootBase _
  have ht := hs.weyl_preimage (by
    intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact G.rootBase.isPos_of_mem_support i.property) w
  have he : {r | G.rootBase.IsPos r ∧
      G.rootSystem.weylGroupToPerm w⁻¹ r ∈ ({(i : G.rootIndex)} : Set G.rootIndex)} =
        rankOneRootSet G w i := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, rankOneRootSet]
    constructor
    · intro h
      have h' := congrArg (G.rootSystem.weylGroupToPerm w) h.2
      simpa only [map_inv, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using h'
    · intro h
      subst r
      exact ⟨hw, by simp only [map_inv, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]⟩
  rwa [he] at ht

/-- The added simple-root direction is disjoint from the preceding left inversions. -/
theorem rankOneRoot_disjoint :
    Disjoint (leftRootInversionIndices G.rootBase w) (rankOneRootSet G w i) := by
  apply Set.disjoint_left.mpr
  intro r hr hi
  obtain rfl := Set.mem_singleton_iff.mp hi
  rw [mem_leftRootInversionIndices] at hr
  apply hr.2
  simpa only [map_inv, Equiv.Perm.coe_inv, Equiv.symm_apply_apply] using
    G.rootBase.isPos_of_mem_support i.property

/-- An increasing simple extension splits into its preceding inversions and the added root. -/
theorem rankOneRoot_union (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i)) :
    leftRootInversionIndices G.rootBase (w * RootPairing.weylGroup.ofIdx G.rootSystem i) =
      leftRootInversionIndices G.rootBase w ∪ rankOneRootSet G w i := by
  rw [leftRootInversionIndices_mul_simple G.rootBase w i hw]
  ext r
  simp only [Set.mem_insert_iff, Set.mem_union, rankOneRootSet, Set.mem_singleton_iff]
  tauto

end
end SchubertGeometry
