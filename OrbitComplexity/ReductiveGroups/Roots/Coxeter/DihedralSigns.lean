import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootSums

/-!
# Root signs in a two-simple-root integral span

A positive root in the integral span of two distinct simple roots has
nonnegative coefficients on those roots. Hence a Weyl element sending both
simples negative sends every such positive root negative. Crystallographic
reflection formulas keep all two-letter prefix roots in this integral span.
-/

noncomputable section

namespace ReductiveGroups

open scoped BigOperators

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- Positive roots in the prescribed integral pair span have nonnegative
integral coefficients on the two simple roots. -/
theorem positive_root_pair_coefficients (b : P.Base) (i j : b.support) (hij : i ≠ j)
    (k : ι) (hk : b.IsPos k)
    (hspan : P.root k ∈ Submodule.span ℤ ({P.root i, P.root j} : Set M)) :
    ∃ a c : ℤ, 0 ≤ a ∧ 0 ≤ c ∧ P.root k = a • P.root i + c • P.root j := by
  classical
  obtain ⟨a, c, heq⟩ := Submodule.mem_span_pair.mp hspan
  let f : ι → ℤ := Pi.single (i : ι) a + Pi.single (j : ι) c
  have hij' : (i : ι) ≠ (j : ι) := fun h => hij (Subtype.ext h)
  have hfi : f i = a := by simp [f, hij']
  have hfj : f j = c := by simp [f, hij'.symm]
  have hsupport : Function.support f ⊆ b.support := by
    intro x hx
    by_cases hxi : x = (i : ι)
    · simp [hxi]
    by_cases hxj : x = (j : ι)
    · simp [hxj]
    have hz : f x = 0 := by simp [f, hxi, hxj]
    exact (hx hz).elim
  have hsum : P.root k = ∑ x ∈ b.support, f x • P.root x := by
    rw [← heq]
    simp [f, Pi.single_apply, add_smul, Finset.sum_add_distrib, i.property, j.property]
  have hsign := b.pos_or_neg_of_sum_smul_root_mem f
    (by rw [← hsum]; exact Set.mem_range_self k) hsupport
  have hfpos : 0 < f := hsign.resolve_right (by
    intro hfneg
    have hheight := b.height_eq_sum hsum
    have hn : ∑ x ∈ b.support, f x ≤ 0 := Finset.sum_nonpos (fun x _ => hfneg.le x)
    change 0 < b.height k at hk
    omega)
  exact ⟨a, c, by simpa only [Pi.zero_apply, hfi] using hfpos.le i,
    by simpa only [Pi.zero_apply, hfj] using hfpos.le j, heq.symm⟩

/-- The equality is

```lean
b.height k = a * b.height i + c * b.height j
```
-/
theorem height_of_root_eq_zsmul_add (b : P.Base) (i j k : ι) (a c : ℤ)
    (heq : P.root k = a • P.root i + c • P.root j) :
    b.height k = a * b.height i + c * b.height j := by
  have he : P.rootSpanMem ℤ k = a • P.rootSpanMem ℤ i + c • P.rootSpanMem ℤ j := by
    apply Subtype.ext
    exact heq
  have hh := congrArg (rootLatticeHeight b) he
  simpa only [map_add, map_smul, rootLatticeHeight_root, smul_eq_mul] using hh

/-- The inverse/sign convention is not needed here: any Weyl
element sending both simple roots negative sends their positive pair-span roots negative. -/
theorem DihedralSigns.negative_of_positive_root_mem_pairSpan (b : P.Base)
    (w : P.weylGroup) (i j : b.support) (hij : i ≠ j)
    (hi : b.height (P.weylGroupToPerm w i) < 0)
    (hj : b.height (P.weylGroupToPerm w j) < 0)
    (k : ι) (hk : b.IsPos k)
    (hspan : P.root k ∈ Submodule.span ℤ ({P.root i, P.root j} : Set M)) :
    b.height (P.weylGroupToPerm w k) < 0 := by
  obtain ⟨a, c, ha, hc, heq⟩ := positive_root_pair_coefficients b i j hij k hk hspan
  have hne : a ≠ 0 ∨ c ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    exact P.ne_zero k (by simpa only [h.1, h.2, zero_smul, zero_add] using heq)
  have himage : P.root (P.weylGroupToPerm w k) =
      a • P.root (P.weylGroupToPerm w i) + c • P.root (P.weylGroupToPerm w j) := by
    have hh := congrArg (RootPairing.Equiv.weightHom P w.val) heq
    simp only [map_add, map_zsmul] at hh
    change w • P.root k = a • (w • P.root i) + c • (w • P.root j) at hh
    simpa only [P.weylGroup_apply_root] using hh
  rw [height_of_root_eq_zsmul_add b _ _ _ a c himage]
  rcases hne with ha' | hc'
  · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg (lt_of_le_of_ne ha (Ne.symm ha')) hi)
      (mul_nonpos_of_nonneg_of_nonpos hc hj.le)
  · exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha hi.le)
      (mul_neg_of_pos_of_neg (lt_of_le_of_ne hc (Ne.symm hc')) hj)

variable [P.IsCrystallographic]

omit [CharZero R] in
/-- The equality is

```lean
P.reflection i (P.root k) = P.root k - (P.pairingIn ℤ k i) • P.root i
```
-/
theorem reflection_root_eq_sub_zsmul (i k : ι) :
    P.reflection i (P.root k) = P.root k - (P.pairingIn ℤ k i) • P.root i := by
  rw [P.reflection_apply_root, ← P.algebraMap_pairingIn ℤ k i]
  change P.root k - (P.pairingIn ℤ k i : R) • P.root i = _
  rw [Int.cast_smul_eq_zsmul]

omit [CharZero R] in
/-- Crystallographic reflection in either member of the pair preserves the
integral pair span. -/
theorem reflection_mem_simplePairSpan (b : P.Base) (i j k : b.support)
    (hk : k = i ∨ k = j) {x : M}
    (hx : x ∈ Submodule.span ℤ ({P.root i, P.root j} : Set M)) :
    P.reflection k x ∈ Submodule.span ℤ ({P.root i, P.root j} : Set M) := by
  have hkspan : P.root k ∈ Submodule.span ℤ ({P.root i, P.root j} : Set M) :=
    Submodule.subset_span (by rcases hk with rfl | rfl <;> simp)
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy with rfl | rfl <;> rw [reflection_root_eq_sub_zsmul] <;>
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp)) (Submodule.smul_mem _ _ hkspan)
  | zero => simpa only [map_zero] using (Submodule.zero_mem _)
  | add x y _ _ ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x _ ih => simpa only [map_zsmul] using Submodule.smul_mem _ a ih

omit [CharZero R] in
/-- For these parameters,

```lean
simpleReflectionWord b l x ∈ Submodule.span ℤ ({P.root i, P.root j} : Set M)
```
-/
theorem simpleReflectionWord_mem_simplePairSpan (b : P.Base) (i j : b.support)
    (l : List b.support) (hl : ∀ k ∈ l, k = i ∨ k = j) {x : M}
    (hx : x ∈ Submodule.span ℤ ({P.root i, P.root j} : Set M)) :
    simpleReflectionWord b l x ∈ Submodule.span ℤ ({P.root i, P.root j} : Set M) := by
  induction l with
  | nil => exact hx
  | cons k l ih =>
    change P.reflection k (simpleReflectionWord b l x) ∈ _
    exact reflection_mem_simplePairSpan b i j k (hl k (by simp))
      (ih (fun t ht => hl t (List.mem_cons_of_mem _ ht)))

omit [CharZero R] in
/-- For these parameters,

```lean
P.root (P.weylGroupToPerm (simpleWeylWord b l) k) ∈
      Submodule.span ℤ ({P.root i, P.root j} : Set M)
```
-/
theorem simpleWeylWord_root_mem_simplePairSpan (b : P.Base) (i j : b.support)
    (l : List b.support) (hl : ∀ k ∈ l, k = i ∨ k = j)
    (k : b.support) (hk : k = i ∨ k = j) :
    P.root (P.weylGroupToPerm (simpleWeylWord b l) k) ∈
      Submodule.span ℤ ({P.root i, P.root j} : Set M) := by
  rw [simpleWeylWord_root]
  exact simpleReflectionWord_mem_simplePairSpan b i j l hl
    (Submodule.subset_span (by rcases hk with rfl | rfl <;> simp))

end ReductiveGroups
