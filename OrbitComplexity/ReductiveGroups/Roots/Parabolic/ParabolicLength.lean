import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicSubgroup

/-!
# Length additivity for minimal right parabolic representatives

Apply exchange to a minimum-length representative word followed by
an allowed-letter prefix. Deleting in the prefix contradicts coset
minimality; deleting in the allowed suffix contradicts its reducedness.
Consequently each step of a reduced parabolic word increases length.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- the exchange theorem with the deleted position exposed
as a list index. -/
theorem simpleWeylWord_exchange_eraseIdx (b : P.Base) (l : List b.support)
    (i : b.support) (hneg : b.height (P.weylGroupToPerm (simpleWeylWord b l) i) < 0) :
    ∃ t < l.length, simpleWeylWord b (l.eraseIdx t) =
      simpleWeylWord b l * RootPairing.weylGroup.ofIdx P i := by
  obtain ⟨pre, j, post, hword, _, hprod, _⟩ := simpleWeylWord_exchange b l i hneg
  refine ⟨pre.length, ?_, ?_⟩
  · simp only [hword, List.length_append, List.length_singleton]
    omega
  · have herase : l.eraseIdx pre.length = pre ++ post := by
      rw [hword, List.append_assoc, List.eraseIdx_append_of_length_le (le_refl _)]
      simp
    rw [herase]
    exact hprod.symm

/-- A reduced allowed-letter word remains ascending when appended to a
minimum-length representative. This is proved by exchange, not
assumed as an alternative definition of the representative. -/
theorem isPos_parabolic_prefix_of_minimal_right (b : P.Base) (J : Set b.support)
    (d : P.weylGroup) (hd : IsMinimalRightParabolic b J d)
    (k : List b.support) (hk : ∀ j ∈ k, j ∈ J) (i : b.support) (hi : i ∈ J)
    (hred : rootInversionCount b (simpleWeylWord b k * RootPairing.weylGroup.ofIdx P i) =
      k.length + 1) : b.IsPos (P.weylGroupToPerm (d * simpleWeylWord b k) i) := by
  by_contra hpos
  obtain ⟨l, hl, hllen⟩ := InversionLength.exists_of_inversionCount_length b d
  have hneg : b.height (P.weylGroupToPerm (simpleWeylWord b (l ++ k)) i) < 0 := by
    rw [simpleWeylWord_append, hl]
    exact (root_height_neg_iff_not_isPos b _).mpr hpos
  obtain ⟨t, ht, hdel⟩ := simpleWeylWord_exchange_eraseIdx b (l ++ k) i hneg
  by_cases htl : t < l.length
  · rw [List.eraseIdx_append_of_lt_length htl] at hdel
    simp only [simpleWeylWord_append, hl] at hdel
    let c := simpleWeylWord b k * RootPairing.weylGroup.ofIdx P i * (simpleWeylWord b k)⁻¹
    have hkJ := SimpleWeylWord.mem_standardParabolicSubgroup b J k hk
    have hc : c ∈ standardParabolicSubgroup b J :=
      (standardParabolicSubgroup b J).mul_mem
        ((standardParabolicSubgroup b J).mul_mem hkJ
          (simple_mem_standardParabolicSubgroup b J i hi))
        ((standardParabolicSubgroup b J).inv_mem hkJ)
    have hshort : simpleWeylWord b (l.eraseIdx t) = d * c := by
      calc
        simpleWeylWord b (l.eraseIdx t) =
            (simpleWeylWord b (l.eraseIdx t) * simpleWeylWord b k) *
              (simpleWeylWord b k)⁻¹ := by simp
        _ = (d * simpleWeylWord b k * RootPairing.weylGroup.ofIdx P i) *
              (simpleWeylWord b k)⁻¹ := by rw [hdel]
        _ = d * c := by simp only [c, mul_assoc]
    have hmin := hd c hc
    rw [← hshort] at hmin
    have hbound := RootInversionCount.simpleWeylWord_le_length b (l.eraseIdx t)
    have hlen := List.length_eraseIdx_add_one htl
    omega
  · have hle : l.length ≤ t := le_of_not_gt htl
    rw [List.eraseIdx_append_of_length_le hle] at hdel
    simp only [simpleWeylWord_append, hl] at hdel
    have he : simpleWeylWord b (k.eraseIdx (t - l.length)) =
        simpleWeylWord b k * RootPairing.weylGroup.ofIdx P i :=
      mul_left_cancel (by simpa only [mul_assoc] using hdel)
    have htk : t - l.length < k.length := by
      simp only [List.length_append] at ht
      omega
    have hlen := List.length_eraseIdx_add_one htk
    have hbound := RootInversionCount.simpleWeylWord_le_length b (k.eraseIdx (t - l.length))
    rw [he, hred] at hbound
    omega

/-- Every reduced word in the parabolic simples adds its full length to
a minimum-length right-coset representative. -/
theorem RootInversionCount.mul_parabolic_word_of_minimal_right (b : P.Base)
    (J : Set b.support) (d : P.weylGroup) (hd : IsMinimalRightParabolic b J d)
    (l : List b.support) (hl : ∀ i ∈ l, i ∈ J)
    (hred : rootInversionCount b (simpleWeylWord b l) = l.length) :
    rootInversionCount b (d * simpleWeylWord b l) = rootInversionCount b d + l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [simpleWeylWord]
  | append_singleton l i ih =>
    have hl' : ∀ j ∈ l, j ∈ J := fun j hj => hl j (List.mem_append_left _ hj)
    have hi : i ∈ J := hl i (by simp)
    have hred' := RootInversionCount.prefix_of_reduced_append_singleton b l i hred
    have hlast : rootInversionCount b (simpleWeylWord b l * RootPairing.weylGroup.ofIdx P i) =
        l.length + 1 := by
      simpa only [simpleWeylWord_append, simpleWeylWord, mul_one,
        List.length_append, List.length_singleton] using hred
    have hpos := isPos_parabolic_prefix_of_minimal_right b J d hd l hl' i hi hlast
    simp only [simpleWeylWord_append, simpleWeylWord, mul_one, ← mul_assoc,
      List.length_append, List.length_singleton]
    rw [rootInversionCount_mul_simple_of_pos b _ i hpos, ih hl' hred', Nat.add_assoc]

/-- Inversion length is additive on a minimal representative times
any element of the generated parabolic subgroup. -/
theorem RootInversionCount.mul_parabolic_of_minimal_right (b : P.Base)
    (J : Set b.support) (d a : P.weylGroup) (hd : IsMinimalRightParabolic b J d)
    (ha : a ∈ standardParabolicSubgroup b J) :
    rootInversionCount b (d * a) = rootInversionCount b d + rootInversionCount b a := by
  obtain ⟨l, hl, hprod, hlen⟩ := exists_reduced_standardParabolic_word b J a ha
  have hred : rootInversionCount b (simpleWeylWord b l) = l.length := by rw [hprod, hlen]
  simpa only [hprod, hlen] using
    RootInversionCount.mul_parabolic_word_of_minimal_right b J d hd l hl hred

end ReductiveGroups
