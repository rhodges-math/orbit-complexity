import OrbitComplexity.ReductiveGroups.Roots.Inversions.InversionLength

/-!
# Inversions of a length-additive Weyl product

All lengths in the statements are the cardinalities of the inversion
sets. Choose an expression attaining that cardinality. Additivity forces every
successive simple-root image to be positive, so the ordinary insertion formula
gives the product decomposition. Positivity of the transported image
then follows from its inclusion in the product's inversion set.

This supplies the root-space assertion `I_L(w) = I_L(a) ⊔ a(I_L(d))` used in
the proof of  (2).

-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- A transported positive inversion of the second factor cannot be a left
inversion of the first factor, regardless of whether its image is positive. -/
theorem leftRootInversions_disjoint_weyl_image (b : P.Base) (a d : P.weylGroup) :
    Disjoint (leftRootInversions b a)
      ((fun β : M => a • β) '' leftRootInversions b d) := by
  rw [Set.disjoint_left]
  intro β hβ hγ
  obtain ⟨γ, ⟨i, hi, rfl⟩, rfl⟩ := hγ
  change a • P.root i ∈ leftRootInversions b a at hβ
  rw [P.weylGroup_apply_root, root_mem_leftRootInversions,
    mem_leftRootInversionIndices] at hβ
  exact hβ.2 (by
    simpa only [map_inv, Equiv.Perm.coe_inv, Equiv.symm_apply_apply] using hi.1)

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- Appending an arbitrary simple word increases inversion count by at
most the word's length. -/
theorem rootInversionCount_mul_simpleWeylWord_le (b : P.Base) (a : P.weylGroup)
    (l : List b.support) :
    rootInversionCount b (a * simpleWeylWord b l) ≤ rootInversionCount b a + l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [simpleWeylWord]
  | append_singleton l i ih =>
    have hstep := rootInversionCount_mul_simple_le b (a * simpleWeylWord b l) i
    have hbound := hstep.trans (Nat.add_le_add_right ih 1)
    simpa only [simpleWeylWord_append, simpleWeylWord, mul_one, List.length_append,
      List.length_singleton, mul_assoc, Nat.add_assoc] using hbound

/-- Subadditivity follows from an expression attaining the second
factor's inversion count. -/
theorem rootInversionCount_mul_le (b : P.Base) (a d : P.weylGroup) :
    rootInversionCount b (a * d) ≤ rootInversionCount b a + rootInversionCount b d := by
  obtain ⟨l, hl, hlength⟩ := InversionLength.exists_of_inversionCount_length b d
  simpa only [hl, hlength] using rootInversionCount_mul_simpleWeylWord_le b a l

/-- When an expression attains both relevant count bounds, each of its final
simple reflections inserts a positive inversion for both products. -/
theorem LeftRootInversions.mul_simpleWeylWord_of_count_eq_length (b : P.Base)
    (a : P.weylGroup) (l : List b.support)
    (hl : rootInversionCount b (simpleWeylWord b l) = l.length)
    (ha : rootInversionCount b (a * simpleWeylWord b l) =
      rootInversionCount b a + l.length) :
    leftRootInversions b (a * simpleWeylWord b l) = leftRootInversions b a ∪
      (fun β : M => a • β) '' leftRootInversions b (simpleWeylWord b l) := by
  induction l using List.reverseRecOn with
  | nil => simp [simpleWeylWord]
  | append_singleton l i ih =>
    have hl' : rootInversionCount b
        (simpleWeylWord b l * RootPairing.weylGroup.ofIdx P i) = l.length + 1 := by
      simpa only [simpleWeylWord_append, simpleWeylWord, mul_one,
        List.length_append, List.length_singleton] using hl
    have ha' : rootInversionCount b
        ((a * simpleWeylWord b l) * RootPairing.weylGroup.ofIdx P i) =
          rootInversionCount b a + l.length + 1 := by
      simpa only [simpleWeylWord_append, simpleWeylWord, mul_one,
        List.length_append, List.length_singleton, mul_assoc, Nat.add_assoc] using ha
    have hlbound := RootInversionCount.simpleWeylWord_le_length b l
    have hlstep := rootInversionCount_mul_simple_le b (simpleWeylWord b l) i
    have hlprev : rootInversionCount b (simpleWeylWord b l) = l.length := by omega
    have habound := rootInversionCount_mul_simpleWeylWord_le b a l
    have hastep := rootInversionCount_mul_simple_le b (a * simpleWeylWord b l) i
    have haprev : rootInversionCount b (a * simpleWeylWord b l) =
        rootInversionCount b a + l.length := by omega
    have hlpos : b.IsPos (P.weylGroupToPerm (simpleWeylWord b l) i) := by
      by_contra hneg
      have h := rootInversionCount_mul_simple_of_neg b (simpleWeylWord b l) i
        ((root_height_neg_iff_not_isPos b _).mpr hneg)
      omega
    have hapos : b.IsPos (P.weylGroupToPerm (a * simpleWeylWord b l) i) := by
      by_contra hneg
      have h := rootInversionCount_mul_simple_of_neg b (a * simpleWeylWord b l) i
        ((root_height_neg_iff_not_isPos b _).mpr hneg)
      omega
    have hprev := ih hlprev haprev
    simp only [simpleWeylWord_append, simpleWeylWord, mul_one]
    rw [← mul_assoc, leftRootInversions_mul_simple b _ i hapos,
      leftRootInversions_mul_simple b _ i hlpos, hprev, Set.image_insert_eq]
    simp only [Set.union_insert, mul_smul]

/-- Inversion-count additivity gives the ordinary left inversion
decomposition, with the Weyl image of the second inversion set. -/
theorem leftRootInversions_mul_of_count_add (b : P.Base) (a d : P.weylGroup)
    (hadd : rootInversionCount b (a * d) = rootInversionCount b a + rootInversionCount b d) :
    leftRootInversions b (a * d) = leftRootInversions b a ∪
      (fun β : M => a • β) '' leftRootInversions b d := by
  obtain ⟨l, rfl, hlength⟩ := InversionLength.exists_of_inversionCount_length b d
  apply LeftRootInversions.mul_simpleWeylWord_of_count_eq_length b a l hlength.symm
  simpa only [hlength] using hadd

/-- Every transported inversion index is positive under count additivity. -/
theorem weyl_image_inversions_isPos_of_count_add (b : P.Base) (a d : P.weylGroup)
    (hadd : rootInversionCount b (a * d) = rootInversionCount b a + rootInversionCount b d)
    {i : ι} (hi : i ∈ leftRootInversionIndices b d) :
    b.IsPos (P.weylGroupToPerm a i) := by
  have hmem : a • P.root i ∈ leftRootInversions b (a * d) := by
    rw [leftRootInversions_mul_of_count_add b a d hadd]
    exact Or.inr ⟨P.root i, ⟨i, hi, rfl⟩, rfl⟩
  rw [P.weylGroup_apply_root, root_mem_leftRootInversions] at hmem
  exact hmem.1

/-- The transported root set consists of positive roots. -/
theorem InversionProduct.inversions_subset_positive_of_count_add (b : P.Base) (a d : P.weylGroup)
    (hadd : rootInversionCount b (a * d) = rootInversionCount b a + rootInversionCount b d) :
    (fun β : M => a • β) '' leftRootInversions b d ⊆ P.root '' {i | b.IsPos i} := by
  rintro β ⟨γ, ⟨i, hi, rfl⟩, rfl⟩
  exact ⟨P.weylGroupToPerm a i,
    weyl_image_inversions_isPos_of_count_add b a d hadd hi,
    (P.weylGroup_apply_root a i).symm⟩

end ReductiveGroups
