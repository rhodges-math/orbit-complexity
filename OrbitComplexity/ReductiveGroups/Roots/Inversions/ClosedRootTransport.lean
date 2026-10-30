import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootClosedSets

/-!
# Transport of closed positive-root sets

Positive integral root closure is preserved by Weyl transport followed by restriction
to positive roots, and by intersection with a linear submodule.
-/

noncomputable section
namespace ReductiveGroups
variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- Weyl transport preserves closed positive root sets after restriction to positive roots. -/
theorem IsPositiveRootClosed.weyl_preimage {b : P.Base} {S : Set ι}
    (hS : IsPositiveRootClosed b S) (hpos : ∀ i ∈ S, b.IsPos i)
    (w : P.weylGroup) :
    IsPositiveRootClosed b {i | b.IsPos i ∧ P.weylGroupToPerm w⁻¹ i ∈ S} := by
  intro β hβ hcl
  refine ⟨hβ, ?_⟩
  obtain ⟨l, hl, hsum⟩ := exists_root_list_of_mem_closure_image hcl
  have hsum' : ((l.map (P.weylGroupToPerm w⁻¹)).map P.root).sum =
      P.root (P.weylGroupToPerm w⁻¹ β) := by
    have he := congrArg (fun v : M => w⁻¹ • v) hsum
    simp only [List.smul_sum, List.map_map] at he
    simpa only [List.map_map, Function.comp_def, P.weylGroup_apply_root] using he
  have hpos' : ∀ i ∈ l.map (P.weylGroupToPerm w⁻¹), b.IsPos i := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact hpos _ (hl j hj).2
  apply hS _ (isPos_of_positive_root_sum b _ _ hpos' hsum')
  rw [← hsum']
  apply AddSubmonoid.list_sum_mem
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  exact AddSubmonoid.subset_closure ⟨_, (hl j hj).2, rfl⟩

/-- Positive roots contained in a linear submodule form a closed root set. -/
theorem isPositiveRootClosed_submodule (b : P.Base) (V : Submodule R M) :
    IsPositiveRootClosed b {i | b.IsPos i ∧ P.root i ∈ V} := by
  intro β hβ hcl
  refine ⟨hβ, ?_⟩
  apply (AddSubmonoid.closure_le.mpr ?_ :
    AddSubmonoid.closure (P.root '' {i | b.IsPos i ∧ P.root i ∈ V}) ≤ V.toAddSubmonoid) hcl
  rintro v ⟨i, hi, rfl⟩
  exact hi.2

end ReductiveGroups
