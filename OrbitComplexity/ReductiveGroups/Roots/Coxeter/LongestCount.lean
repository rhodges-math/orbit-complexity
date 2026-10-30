import OrbitComplexity.ReductiveGroups.Roots.Coxeter.Longest

/-!
# Counting the inversions of the longest Weyl element

The inverse of the longest element sends every positive root to a negative root.
Its inversion set therefore consists of all positive roots, so its inversion
count is the cardinality of the positive root indices.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- The inversion indices of the longest Weyl element are exactly the positive root indices. -/
theorem leftRootInversionIndices_longest (b : P.Base) :
    leftRootInversionIndices b (longestWeylElement b) = {i | b.IsPos i} := by
  ext i
  simp only [mem_leftRootInversionIndices, Set.mem_ofPred_eq]
  constructor
  · exact And.left
  · intro hi
    refine ⟨hi, ?_⟩
    intro hneg
    have h := longestWeylElement_not_isPos b hneg
    apply h
    simpa only [map_inv, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using hi

/-- The longest Weyl element has as many inversions as there are positive roots. -/
theorem rootInversionCount_longest (b : P.Base) :
    rootInversionCount b (longestWeylElement b) = {i | b.IsPos i}.ncard := by
  rw [rootInversionCount, leftRootInversions, leftRootInversionIndices_longest]
  exact Set.ncard_image_of_injective _ P.root.injective

end ReductiveGroups
