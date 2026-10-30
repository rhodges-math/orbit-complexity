import OrbitComplexity.ReductiveGroups.Roots.Inversions.InversionCone

/-!
# Positive Root Closed Sets

Closed sets of positive roots: a positive root in the nonnegative
integral cone of the set belongs to the set. Left inversion sets and their
complements in the positive roots are closed. -/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- A set of root indices is closed among the positive roots when every
positive root lying in the nonnegative integral cone of its roots belongs
to it. -/
def IsPositiveRootClosed (b : P.Base) (S : Set ι) : Prop :=
  ∀ β, b.IsPos β → P.root β ∈ AddSubmonoid.closure (P.root '' S) → β ∈ S

omit [CharZero R] in
/-- The equality is

```lean
∃ l : List ι, (∀ i ∈ l, i ∈ S) ∧ (l.map P.root).sum = β
```
-/
theorem exists_root_list_of_mem_closure_image {S : Set ι} {β : M}
    (hβ : β ∈ AddSubmonoid.closure (P.root '' S)) :
    ∃ l : List ι, (∀ i ∈ l, i ∈ S) ∧ (l.map P.root).sum = β := by
  induction hβ using AddSubmonoid.closure_induction with
  | mem β hβ =>
    obtain ⟨i, hi, rfl⟩ := hβ
    exact ⟨[i], by simpa using hi, by simp⟩
  | zero => exact ⟨[], by simp, by simp⟩
  | add β γ _ _ ihβ ihγ =>
    obtain ⟨l, hl, hls⟩ := ihβ
    obtain ⟨m, hm, hms⟩ := ihγ
    refine ⟨l ++ m, ?_, ?_⟩
    · intro i hi
      exact (List.mem_append.mp hi).elim (hl i) (hm i)
    · simp only [List.map_append, List.sum_append, hls, hms]

/-- The positive roots form a closed set. -/
theorem isPositiveRootClosed_isPos (b : P.Base) : IsPositiveRootClosed b {i | b.IsPos i} :=
  fun _ hβ _ => hβ

/-- Intersections of closed sets are closed. -/
theorem IsPositiveRootClosed.inter {b : P.Base} {S T : Set ι}
    (hS : IsPositiveRootClosed b S) (hT : IsPositiveRootClosed b T) :
    IsPositiveRootClosed b (S ∩ T) := by
  intro β hβ hcl
  refine ⟨hS β hβ (AddSubmonoid.closure_mono (Set.image_mono Set.inter_subset_left) hcl),
    hT β hβ (AddSubmonoid.closure_mono (Set.image_mono Set.inter_subset_right) hcl)⟩

/-- The positive roots that are not left inversions of `w` form a closed set. -/
theorem PositiveRootClosedSets.isPositiveRootClosed (b : P.Base) (w : P.weylGroup) :
    IsPositiveRootClosed b {i | b.IsPos i ∧ i ∉ leftRootInversionIndices b w} := by
  intro β hβ hcl
  refine ⟨hβ, ?_⟩
  obtain ⟨l, hl, hsum⟩ := exists_root_list_of_mem_closure_image hcl
  intro hinv
  apply (root_height_neg_iff_not_isPos b _).mp hinv.2
  apply isPos_of_positive_root_sum b (l.map (P.weylGroupToPerm w⁻¹)) _
  · intro j hj
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
    have hkS := hl k hk
    by_contra hneg
    exact hkS.2 ⟨hkS.1, (root_height_neg_iff_not_isPos b _).mpr hneg⟩
  · have hlin := congrArg (fun v : M => w⁻¹ • v) hsum
    simp only [List.smul_sum, List.map_map] at hlin
    simpa only [List.map_map, Function.comp_def, P.weylGroup_apply_root] using hlin

variable [Finite ι] [P.IsCrystallographic] [IsDomain R]

/-- Left inversion sets are closed. -/
theorem LeftRootInversionIndices.isPositiveRootClosed (b : P.Base) (w : P.weylGroup) :
    IsPositiveRootClosed b (leftRootInversionIndices b w) := by
  intro β _ hβ
  obtain ⟨β', hβ', he⟩ := (root_mem_inversionClosure_iff b w β).mp hβ
  rwa [P.root.injective he] at hβ'


end ReductiveGroups
