import OrbitComplexity.ReductiveGroups.Roots.Coxeter.DihedralLength
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.DihedralSigns

/-!
# The rank-two common-descent reduction

If a Weyl element sends both simple roots of a pair negative, every
positive prefix root of a reduced word in those two letters is also sent
negative. Each appended simple reflection therefore lowers inversion
count by one. Applying the proved braid-word length gives the common-descent
diamond required for the presentation word-property argument.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- Every reduced two-letter word decreases length at every step when
both corresponding simple-root images are initially negative. -/
theorem RootInversionCount.mul_two_letter_word_of_negative (b : P.Base)
    (w : P.weylGroup) (i j : b.support) (hij : i ≠ j)
    (hi : b.height (P.weylGroupToPerm w i) < 0)
    (hj : b.height (P.weylGroupToPerm w j) < 0)
    (l : List b.support) (hl : ∀ k ∈ l, k = i ∨ k = j)
    (hred : rootInversionCount b (simpleWeylWord b l) = l.length) :
    rootInversionCount b (w * simpleWeylWord b l) + l.length = rootInversionCount b w := by
  induction l using List.reverseRecOn with
  | nil => simp [simpleWeylWord]
  | append_singleton l k ih =>
    have hlast : k = i ∨ k = j := hl k (by simp)
    have hletters : ∀ t ∈ l, t = i ∨ t = j :=
      fun t ht => hl t (List.mem_append_left _ ht)
    have hred' : rootInversionCount b
        (simpleWeylWord b l * RootPairing.weylGroup.ofIdx P k) = l.length + 1 := by
      simpa only [simpleWeylWord_append, simpleWeylWord, mul_one,
        List.length_append, List.length_singleton] using hred
    have hbound := RootInversionCount.simpleWeylWord_le_length b l
    have hstep := rootInversionCount_mul_simple_le b (simpleWeylWord b l) k
    have hprev : rootInversionCount b (simpleWeylWord b l) = l.length := by omega
    have hpos : b.IsPos (P.weylGroupToPerm (simpleWeylWord b l) k) := by
      by_contra hn
      have hneg := rootInversionCount_mul_simple_of_neg b (simpleWeylWord b l) k
        ((root_height_neg_iff_not_isPos b _).mpr hn)
      omega
    have hpair := simpleWeylWord_root_mem_simplePairSpan b i j l hletters k hlast
    have himage := DihedralSigns.negative_of_positive_root_mem_pairSpan b w i j hij hi hj
      (P.weylGroupToPerm (simpleWeylWord b l) k) hpos hpair
    have hnegative : b.height (P.weylGroupToPerm (w * simpleWeylWord b l) k) < 0 := by
      simpa only [map_mul, Equiv.Perm.mul_apply] using himage
    have hcount := rootInversionCount_mul_simple_of_neg b (w * simpleWeylWord b l) k hnegative
    have hind := ih hletters hprev
    simp only [simpleWeylWord_append, simpleWeylWord, mul_one,
      List.length_append, List.length_singleton, ← mul_assoc]
    omega

/-- The braid word lowers length by its complete dihedral length
when both simple-root images are negative. -/
theorem RootInversionCount.mul_braidWord_of_negative (b : P.Base)
    (w : P.weylGroup) (i j : b.support) (hij : i ≠ j)
    (hi : b.height (P.weylGroupToPerm w i) < 0)
    (hj : b.height (P.weylGroupToPerm w j) < 0) :
    rootInversionCount b
        (w * simpleWeylWord b (CoxeterSystem.braidWord (simpleCoxeterMatrix b) i j)) +
      simpleCoxeterMatrix b i j = rootInversionCount b w := by
  have h := RootInversionCount.mul_two_letter_word_of_negative b w i j hij hi hj
    (CoxeterSystem.braidWord (simpleCoxeterMatrix b) i j)
    (fun k hk => mem_alternatingWord_two_letters b i j _ hk)
    (by simpa only [CoxeterSystem.length_alternatingWord] using rootInversionCount_braidWord b i j)
  simpa only [CoxeterSystem.length_alternatingWord] using h

/-- The rank-two common-right-descent reduction, stated purely with
inversion counts and simple reflections. -/
theorem RootInversionCount.mul_braidWord_of_common_descents (b : P.Base)
    (w : P.weylGroup) (i j : b.support) (hij : i ≠ j)
    (hi : rootInversionCount b (w * RootPairing.weylGroup.ofIdx P i) < rootInversionCount b w)
    (hj : rootInversionCount b (w * RootPairing.weylGroup.ofIdx P j) < rootInversionCount b w) :
    rootInversionCount b
        (w * simpleWeylWord b (CoxeterSystem.braidWord (simpleCoxeterMatrix b) i j)) +
      simpleCoxeterMatrix b i j = rootInversionCount b w := by
  have hi' : b.height (P.weylGroupToPerm w i) < 0 := by
    rw [root_height_neg_iff_not_isPos]
    intro hpos
    have h := rootInversionCount_mul_simple_of_pos b w i hpos
    omega
  have hj' : b.height (P.weylGroupToPerm w j) < 0 := by
    rw [root_height_neg_iff_not_isPos]
    intro hpos
    have h := rootInversionCount_mul_simple_of_pos b w j hpos
    omega
  exact RootInversionCount.mul_braidWord_of_negative b w i j hij hi' hj'

end ReductiveGroups
