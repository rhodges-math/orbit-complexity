import OrbitComplexity.ReductiveGroups.Roots.Supports.BooleanBondOrder

/-!
# Incompatible crossings of a multiple bond in one Boolean word

The prefix-root witness is extracted from the original inversion
set. Subsequent order arguments refer to positions in the same
distinct-letter word.
-/

noncomputable section
namespace ReductiveGroups

attribute [local instance] Classical.decEq

variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- Every root vector in the prefix-root set comes from one
occurrence of the word, with the preceding prefix acting on
that occurrence's simple root. -/
theorem wordRootSet_mem_exists_occurrence (b : P.Base)
    (l : List b.support) {v : M} (hv : v ∈ wordRootSet b l) :
    ∃ (L : List b.support) (i : b.support) (T : List b.support),
      l = L ++ i :: T ∧ v = simpleReflectionWord b L (P.root (i : ι)) := by
  induction l generalizing v with
  | nil => simp [wordRootSet] at hv
  | cons j l ih =>
      change v ∈ insert (P.root (j : ι))
        ((P.reflection (j : ι)) '' wordRootSet b l) at hv
      rcases Set.mem_insert_iff.mp hv with hj | ⟨w, hw, rfl⟩
      · exact ⟨[], j, l, rfl, by simpa [simpleReflectionWord] using hj⟩
      · obtain ⟨L, i, T, hl, hw'⟩ := ih hw
        refine ⟨j :: L, i, T, ?_, ?_⟩
        · simp [hl]
        · rw [hw']
          rfl

variable [CharZero R] [IsDomain R] [Finite ι]
  [P.IsCrystallographic] [P.IsReduced]

/-- A left inversion of a distinct word has a
prefix-letter witness. The root-index equality uses root
injectivity, rather than identifying roots by their coordinates. -/
theorem leftRootInversion_exists_word_occurrence (b : P.Base)
    (l : List b.support) (hl : l.Nodup) (β : ι)
    (hβ : P.root β ∈ leftRootInversions b (simpleWeylWord b l)) :
    ∃ (L : List b.support) (i : b.support) (T : List b.support),
      l = L ++ i :: T ∧
      β = P.weylGroupToPerm (simpleWeylWord b L) i := by
  rw [LeftRootInversions.simpleWeylWord_eq_wordRootSet_ambient b l hl] at hβ
  obtain ⟨L, i, T, hword, hvec⟩ :=
    wordRootSet_mem_exists_occurrence b l hβ
  refine ⟨L, i, T, hword, ?_⟩
  apply P.root.injective
  rw [simpleWeylWord_root]
  exact hvec

/-- If `j` precedes `q` in a nodup word and `q` lies in a specified prefix or
at its next letter, that prefix contains `j` before every occurrence of `q`. -/
theorem nodup_word_bond_order_in_occurrence
    {α : Type*} [BEq α] [LawfulBEq α]
    (l L T : List α) (i j q : α) (hl : l.Nodup)
    (hword : l = L ++ i :: T)
    (horder : l.idxOf j < l.idxOf q)
    (hq : q = i ∨ q ∈ L) :
    ∃ U V : List α, L = U ++ j :: V ∧ q ∉ U := by
  have hiL : i ∉ L := by
    rw [hword] at hl
    intro hi
    exact (List.nodup_append.mp hl).2.2 i hi i (by simp) rfl
  have hidxi : l.idxOf i = L.length := by
    rw [hword, List.idxOf_append_of_notMem hiL]
    simp
  have hqle : l.idxOf q ≤ l.idxOf i := by
    rcases hq with he | hqL
    · subst q
      exact le_rfl
    · rw [hword, List.idxOf_append_of_mem hqL,
        List.idxOf_append_of_notMem hiL]
      simp only [List.idxOf_cons_self, Nat.add_zero]
      exact Nat.le_of_lt (List.idxOf_lt_length_of_mem hqL)
  have hjL : j ∈ L := by
    have hpref : L <+: l := ⟨i :: T, hword.symm⟩
    apply (hpref.mem_iff_idxOf_lt_length j).mpr
    omega
  obtain ⟨U, V, hL⟩ := List.append_of_mem hjL
  refine ⟨U, V, hL, ?_⟩
  intro hqU
  have hjU : j ∉ U := by
    rw [hword, hL] at hl
    have hnodup := (List.nodup_append.mp hl).1
    intro hj
    exact (List.nodup_append.mp hnodup).2.2 j hj j (by simp) rfl
  have hidxj : l.idxOf j = U.length := by
    rw [hword, hL, List.append_assoc,
      List.idxOf_append_of_notMem hjU]
    simp
  have hidxq : l.idxOf q = U.idxOf q := by
    rw [hword, hL, List.append_assoc,
      List.idxOf_append_of_mem hqU]
  have hlt := List.idxOf_lt_length_of_mem hqU
  omega

/-- A bond letter earlier in the one Boolean word dominates
the later letter's Cartan contribution in every inversion containing
both letters. This includes the case where the later letter is the
initial simple root of the prefix-root witness. -/
theorem LeftRootInversion.bond_coefficient_lower_of_word_order
    (b : P.Base) (l : List b.support) (hl : l.Nodup)
    (β : ι) (hβ : P.root β ∈
      leftRootInversions b (simpleWeylWord b l))
    (j q : b.support) (hjq : j ≠ q)
    (hqβ : simpleRootCoeffInt b β q ≠ 0)
    (horder : l.idxOf j < l.idxOf q) :
    -simpleRootCoeffInt b β q *
        P.pairingIn ℤ (q : ι) (j : ι) ≤
      simpleRootCoeffInt b β j := by
  obtain ⟨L, i, T, hword, hβeq⟩ :=
    leftRootInversion_exists_word_occurrence b l hl β hβ
  have hqEither : q = i ∨ q ∈ L := by
    have hqSupp : q ∈ simpleRootSupportInt b β := hqβ
    rw [hβeq] at hqSupp
    have h := simpleWeylWord_simple_support_subset b L i hqSupp
    simpa only [Set.mem_insert_iff, Set.mem_ofPred_eq] using h
  obtain ⟨U, V, hL, hqU⟩ :=
    nodup_word_bond_order_in_occurrence l L T i j q hl hword
      horder hqEither
  have hiL : i ∉ L := by
    rw [hword] at hl
    intro hi
    exact (List.nodup_append.mp hl).2.2 i hi i (by simp) rfl
  have hLnodup : L.Nodup := by
    rw [hword] at hl
    exact (List.nodup_append.mp hl).1
  have hjU : j ∉ U := by
    rw [hL] at hLnodup
    intro hj
    exact (List.nodup_append.mp hLnodup).2.2 j hj j (by simp) rfl
  have hjV : j ∉ V := by
    rw [hL] at hLnodup
    exact (List.nodup_cons.mp (List.nodup_append.mp hLnodup).2.1).1
  have hiUV : i ∉ U ++ j :: V := by simpa only [← hL] using hiL
  rw [hβeq, hL]
  exact SimpleWeylWord.bond_coefficient_lower_of_order
    b U V i j q hiUV hjU hjV hqU hjq

/-- Every occupied simple coordinate of an inversion of a
distinct word is one of that word's letters. -/
theorem LeftRootInversion.support_letter_mem_word
    (b : P.Base) (l : List b.support) (hl : l.Nodup)
    (β : ι) (hβ : P.root β ∈
      leftRootInversions b (simpleWeylWord b l))
    (j : b.support) (hj : simpleRootCoeffInt b β j ≠ 0) :
    j ∈ l := by
  obtain ⟨L, i, T, hword, hβeq⟩ :=
    leftRootInversion_exists_word_occurrence b l hl β hβ
  have hjsupp : j ∈ simpleRootSupportInt b β := hj
  rw [hβeq] at hjsupp
  have h := simpleWeylWord_simple_support_subset b L i hjsupp
  rw [hword]
  simp only [Set.mem_insert_iff, Set.mem_ofPred_eq] at h
  rcases h with hji | hjL
  · simp [hji]
  · exact List.mem_append.mpr (Or.inl hjL)

/-- the opposite-crossing obstruction for the
left inversion set of one Boolean (distinct-letter) word. The two
coefficient patterns require opposite orders of the same bond letters. -/
theorem BooleanOppositeCrossing.opposite_crossing_not_both_inversions
    (b : P.Base) (l : List b.support) (hl : l.Nodup)
    (p q : b.support)
    (hpq : P.pairingIn ℤ (p : ι) (q : ι) = -2)
    (hqp : P.pairingIn ℤ (q : ι) (p : ι) = -1)
    (β η : ι)
    (hβ : P.root β ∈ leftRootInversions b (simpleWeylWord b l))
    (hη : P.root η ∈ leftRootInversions b (simpleWeylWord b l))
    (hβp : simpleRootCoeffInt b β p = 1)
    (hβq : simpleRootCoeffInt b β q = 2)
    (hηp : simpleRootCoeffInt b η p = 1)
    (hηq : simpleRootCoeffInt b η q = 1) : False := by
  have hpqne : p ≠ q := by
    intro he
    subst q
    rw [RootPairing.pairingIn_same] at hpq
    omega
  have hp : p ∈ l := LeftRootInversion.support_letter_mem_word
    b l hl β hβ p (by rw [hβp]; norm_num)
  have hq : q ∈ l := LeftRootInversion.support_letter_mem_word
    b l hl β hβ q (by rw [hβq]; norm_num)
  have hidxne : l.idxOf p ≠ l.idxOf q := by
    intro he
    exact hpqne ((List.idxOf_inj hp).mp he)
  rcases lt_or_gt_of_ne hidxne with hpBefore | hqBefore
  · have hbound := LeftRootInversion.bond_coefficient_lower_of_word_order
      b l hl β hβ p q hpqne (by rw [hβq]; norm_num) hpBefore
    rw [hβp, hβq, hqp] at hbound
    norm_num at hbound
  · have hbound := LeftRootInversion.bond_coefficient_lower_of_word_order
      b l hl η hη q p hpqne.symm (by rw [hηp]; norm_num) hqBefore
    rw [hηq, hηp, hpq] at hbound
    norm_num at hbound

end ReductiveGroups
