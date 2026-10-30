import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootSums
import OrbitComplexity.ReductiveGroups.Roots.Supports.IndependentNaturalSums
import OrbitComplexity.ReductiveGroups.RootClosure.Basic

/-!
# Integral closure and non-sums for inversion sets

The inverse Weyl action sends both summands negative. Additivity of height
on a root sum proves that their sum, when a root, is again an inversion.
This binary closedness is iterated along the proved ordering of the prescribed
multiset, exactly as in the partial-sum argument. Independence
then forces any natural expression for a root to have total multiplicity one.
-/

noncomputable section

namespace ReductiveGroups

open scoped BigOperators

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- For these parameters,

```lean
k ∈ leftRootInversionIndices b w
```
-/
theorem leftRootInversionIndices_add (b : P.Base) (w : P.weylGroup) {i j k : ι}
    (hi : i ∈ leftRootInversionIndices b w) (hj : j ∈ leftRootInversionIndices b w)
    (hk : P.root k = P.root i + P.root j) : k ∈ leftRootInversionIndices b w := by
  refine ⟨hi.1.add hj.1 hk, ?_⟩
  have he : P.root (P.weylGroupToPerm w⁻¹ k) =
      P.root (P.weylGroupToPerm w⁻¹ i) + P.root (P.weylGroupToPerm w⁻¹ j) := by
    simp only [← P.weylGroup_apply_root, hk, smul_add]
  rw [b.height_add he]
  exact add_neg hi.2 hj.2

/-- Inversion sets are closed under addition whenever the sum is a root. -/
theorem leftRootInversions_add (b : P.Base) (w : P.weylGroup) {β γ : M}
    (hβ : β ∈ leftRootInversions b w) (hγ : γ ∈ leftRootInversions b w)
    (hsum : β + γ ∈ Set.range P.root) : β + γ ∈ leftRootInversions b w := by
  obtain ⟨i, hi, rfl⟩ := hβ
  obtain ⟨j, hj, rfl⟩ := hγ
  obtain ⟨k, hk⟩ := hsum
  exact ⟨k, leftRootInversionIndices_add b w hi hj hk, hk⟩

/-- Iterate binary inversion closure along a prescribed chain of root partial sums. -/
theorem LeftRootInversions.sum_of_root_partial_sums (b : P.Base) (w : P.weylGroup)
    (l : List ι) (hne : l ≠ []) (hinv : ∀ i ∈ l, P.root i ∈ leftRootInversions b w)
    (hpartial : ∀ n : ℕ, 0 < n → n ≤ l.length →
      ((l.take n).map P.root).sum ∈ Set.range P.root) :
    (l.map P.root).sum ∈ leftRootInversions b w := by
  induction l using List.reverseRecOn with
  | nil => exact (hne rfl).elim
  | append_singleton l i ih =>
    by_cases hl : l = []
    · simpa only [hl, List.nil_append, List.map_singleton, List.sum_singleton] using
        hinv i (by simp)
    · have hprev := ih hl (fun j hj => hinv j (List.mem_append_left _ hj))
        (fun n hn hn' => by
          have h := hpartial n hn (by simp only [List.length_append, List.length_singleton]; omega)
          rwa [List.take_append_of_le_length hn'] at h)
      have hlast : P.root i ∈ leftRootInversions b w := hinv i (by simp)
      have hroot := hpartial (l ++ [i]).length (by simp) le_rfl
      simp only [List.take_length, List.map_append, List.map_singleton, List.sum_append,
        List.sum_singleton] at hroot ⊢
      exact leftRootInversions_add b w hprev hlast hroot

variable [Finite ι] [IsDomain R] [P.IsCrystallographic]

/-- the partial-sum argument, applied to a prescribed list of inversions. -/
theorem leftRootInversions_root_sum (b : P.Base) (w : P.weylGroup) (l : List ι)
    (hinv : ∀ j ∈ l, j ∈ leftRootInversionIndices b w) (i : ι)
    (hsum : (l.map P.root).sum = P.root i) : P.root i ∈ leftRootInversions b w := by
  obtain ⟨v, hv, hpartial⟩ := exists_perm_root_partial_sums b l i
    (fun j hj => (hinv j hj).1) hsum
  have hvs : (v.map P.root).sum = P.root i := ((hv.map P.root).sum_eq).trans hsum
  have hvne : v ≠ [] := by
    intro he
    exact P.ne_zero i (by simpa [he] using hvs.symm)
  rw [← hvs]
  apply LeftRootInversions.sum_of_root_partial_sums b w v hvne _ hpartial
  intro j hj
  exact ⟨j, hinv j (hv.mem_iff.mp hj), rfl⟩

omit [Finite ι] [IsDomain R] [P.IsCrystallographic] in
/-- An additive-submonoid expression is expanded into its multiset
of root summands, retaining all repeated copies. -/
theorem exists_root_list_of_mem_inversionClosure (b : P.Base) (w : P.weylGroup)
    {β : M} (hβ : β ∈ AddSubmonoid.closure (leftRootInversions b w)) :
    ∃ l : List ι, (∀ i ∈ l, i ∈ leftRootInversionIndices b w) ∧
      (l.map P.root).sum = β := by
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

/-- A root in the nonnegative integral span of left inversions is
itself a left inversion. The proof uses the prescribed partial-sum chain. -/
theorem root_mem_inversionClosure_iff (b : P.Base) (w : P.weylGroup) (i : ι) :
    P.root i ∈ AddSubmonoid.closure (leftRootInversions b w) ↔
      P.root i ∈ leftRootInversions b w := by
  constructor
  · intro hi
    obtain ⟨l, hl, hsum⟩ := exists_root_list_of_mem_inversionClosure b w hi
    exact leftRootInversions_root_sum b w l hl i hsum
  · intro hi
    exact AddSubmonoid.subset_closure hi

/-- Explicit finite natural-coefficient form of the integral-cone statement. -/
theorem InversionCone.mem_leftRootInversions_iff_finite_sum (b : P.Base) (w : P.weylGroup) (i : ι) :
    P.root i ∈ leftRootInversions b w ↔
      ∃ (t : Finset M) (n : M → ℕ), (↑t : Set M) ⊆ leftRootInversions b w ∧
        ∑ β ∈ t, n β • β = P.root i := by
  rw [← root_mem_inversionClosure_iff b w i, mem_addSubmonoidClosure_iff_finite_sum]

variable [P.IsRootSystem] [P.IsReduced]

/-- Independence for a distinct-simple word forces total multiplicity one
whenever a natural combination of its inversions is a root. -/
theorem inversion_natCoefficientSum_eq_one (b : P.Base) (l : List b.support)
    (hl : l.Nodup) (t : Finset (leftRootInversions b (simpleWeylWord b l)))
    (n : leftRootInversions b (simpleWeylWord b l) → ℕ) (i : ι)
    (hsum : ∑ δ ∈ t, n δ • (δ : M) = P.root i) : ∑ δ ∈ t, n δ = 1 := by
  have hi : P.root i ∈ leftRootInversions b (simpleWeylWord b l) := by
    apply (root_mem_inversionClosure_iff b (simpleWeylWord b l) i).mp
    rw [← hsum]
    exact AddSubmonoid.sum_mem _ (fun δ _ =>
      AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure δ.property) _)
  exact NatCoefficientSum.eq_one_of_linearIndepOn
    (LeftRootInversions.simpleWeylWord_linearIndepOn b l hl) t n hi hsum

/-- No sum with total natural multiplicity at least two is a root. This
includes repeated copies of a single inversion root. -/
theorem inversion_natSum_not_root (b : P.Base) (l : List b.support) (hl : l.Nodup)
    (t : Finset (leftRootInversions b (simpleWeylWord b l)))
    (n : leftRootInversions b (simpleWeylWord b l) → ℕ)
    (hn : 2 ≤ ∑ δ ∈ t, n δ) : (∑ δ ∈ t, n δ • (δ : M)) ∉ Set.range P.root := by
  rintro ⟨i, hi⟩
  have he := inversion_natCoefficientSum_eq_one b l hl t n i hi.symm
  omega

end ReductiveGroups
