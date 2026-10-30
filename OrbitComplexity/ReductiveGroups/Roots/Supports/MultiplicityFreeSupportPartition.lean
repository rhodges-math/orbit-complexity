import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootSums

/-!
# Coefficients and support of a multiplicity-free positive-root sum

Coordinates are taken in the integral root-span basis by
`RootPairing.Base`. List positions retain repeated summands as distinct
occurrences.
-/

noncomputable section

namespace ReductiveGroups

open scoped BigOperators

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- The integral simple-root coefficient, in the root-span basis. -/
def simpleRootCoeffInt (b : P.Base) (β : ι) (i : b.support) : ℤ :=
  (b.toWeightBasisInt.repr (P.rootSpanMem ℤ β)) i

/-- Support in the simple-root basis of the integral root span. -/
def simpleRootSupportInt (b : P.Base) (β : ι) : Set b.support :=
  {i | simpleRootCoeffInt b β i ≠ 0}

/-- The inclusion is

```lean
0 ≤ simpleRootCoeffInt b β i
```
-/
theorem simpleRootCoeffInt_nonneg_of_isPos (b : P.Base) (β : ι)
    (hβ : b.IsPos β) (i : b.support) : 0 ≤ simpleRootCoeffInt b β i := by
  classical
  obtain ⟨f, hfSupport, hfSign, hfRoot⟩ := b.exists_root_eq_sum_int β
  have hfNonneg : ∀ j : ι, 0 ≤ f j := by
    rcases hfSign with hfPos | hfNeg
    · exact fun j => hfPos.le j
    · have hheight : b.height β = ∑ j ∈ b.support, f j := b.height_eq_sum hfRoot
      have hsumNonpos : (∑ j ∈ b.support, f j) ≤ 0 :=
        Finset.sum_nonpos (fun j _ => hfNeg.le j)
      exact False.elim ((not_le.mpr hβ) (hheight ▸ hsumNonpos))
  have hrootSubtype : P.root β =
      ∑ j : b.support, f (j : ι) • P.root (j : ι) := by
    simpa only [b.support.sum_subtype (p := (· ∈ b.support))
      (by simp) (F := inferInstance)] using hfRoot
  have hspan : P.rootSpanMem ℤ β =
      ∑ j : b.support, f (j : ι) • b.toWeightBasisInt j := by
    apply Subtype.ext
    simpa using hrootSubtype
  have hcoord : simpleRootCoeffInt b β i = f i := by
    rw [simpleRootCoeffInt, hspan]
    simp [Finsupp.single_apply]
  rw [hcoord]
  exact hfNonneg i

/-- The equality is

```lean
(l.map (fun γ => simpleRootCoeffInt b γ i)).sum =
      simpleRootCoeffInt b β i
```
-/
theorem simpleRootCoeffInt_list_sum (b : P.Base) (l : List ι) (β : ι)
    (hsum : (l.map P.root).sum = P.root β) (i : b.support) :
    (l.map (fun γ => simpleRootCoeffInt b γ i)).sum =
      simpleRootCoeffInt b β i := by
  have hspan := rootLattice_sum_eq_of_root_sum_eq (P := P) l β hsum
  have h := congrArg (fun x : P.rootSpan ℤ => (b.toWeightBasisInt.repr x) i) hspan
  have heval (z : List (b.support →₀ ℤ)) :
      z.sum i = (z.map fun f => f i).sum := by
    induction z with
    | nil => simp
    | cons f z ih => simp [ih]
  simp only [map_list_sum, heval, List.map_map, Function.comp_def] at h
  exact h

/-- The equality is

```lean
(∑ p : Fin l.length, simpleRootCoeffInt b l[p] i) =
      simpleRootCoeffInt b β i
```
-/
theorem simpleRootCoeffInt_occurrence_sum (b : P.Base) (l : List ι) (β : ι)
    (hsum : (l.map P.root).sum = P.root β) (i : b.support) :
    (∑ p : Fin l.length, simpleRootCoeffInt b l[p] i) =
      simpleRootCoeffInt b β i := by
  have h := simpleRootCoeffInt_list_sum b l β hsum i
  simpa only [← Fin.sum_univ_fun_getElem, List.getElem_map,
    Fin.getElem_fin] using h

/-- Every occurrence in a positive-root expression has nonnegative
coordinates, including when the same root occurs more than once. -/
theorem simpleRootCoeffInt_occurrence_nonneg (b : P.Base) (l : List ι)
    (hpos : ∀ γ ∈ l, b.IsPos γ) (p : Fin l.length) (i : b.support) :
    0 ≤ simpleRootCoeffInt b l[p] i :=
  simpleRootCoeffInt_nonneg_of_isPos b l[p]
    (hpos _ (List.getElem_mem _)) i

/-- The first support-partition step in the multiplicity-free expression
argument. The indices `p q : Fin l.length` distinguish repeated occurrences. -/
theorem MultiplicityFree.positiveRoot_support_partition (b : P.Base)
    (l : List ι) (β : ι)
    (hpos : ∀ γ ∈ l, b.IsPos γ)
    (hsum : (l.map P.root).sum = P.root β)
    (hβ : ∀ i : b.support,
      simpleRootCoeffInt b β i = 0 ∨ simpleRootCoeffInt b β i = 1) :
    (∀ p : Fin l.length, ∀ i : b.support,
      simpleRootCoeffInt b l[p] i = 0 ∨ simpleRootCoeffInt b l[p] i = 1) ∧
    (∀ p q : Fin l.length, p ≠ q →
      Disjoint (simpleRootSupportInt b l[p]) (simpleRootSupportInt b l[q])) ∧
    (∀ i : b.support, i ∈ simpleRootSupportInt b β ↔
      ∃ p : Fin l.length, i ∈ simpleRootSupportInt b l[p]) := by
  classical
  have hunit (p : Fin l.length) (i : b.support) :
      simpleRootCoeffInt b l[p] i = 0 ∨ simpleRootCoeffInt b l[p] i = 1 := by
    have hle : simpleRootCoeffInt b l[p] i ≤ simpleRootCoeffInt b β i := by
      rw [← simpleRootCoeffInt_occurrence_sum b l β hsum i]
      exact Finset.single_le_sum
        (fun q _ => simpleRootCoeffInt_occurrence_nonneg b l hpos q i)
        (Finset.mem_univ p)
    have hge := simpleRootCoeffInt_occurrence_nonneg b l hpos p i
    rcases hβ i with hz | ho <;> omega
  refine ⟨hunit, ?_, ?_⟩
  · intro p q hpq
    apply Set.disjoint_left.mpr
    intro i hip hiq
    change simpleRootCoeffInt b l[p] i ≠ 0 at hip
    change simpleRootCoeffInt b l[q] i ≠ 0 at hiq
    have hpone : simpleRootCoeffInt b l[p] i = 1 := (hunit p i).resolve_left hip
    have hqone : simpleRootCoeffInt b l[q] i = 1 := (hunit q i).resolve_left hiq
    have hpair : simpleRootCoeffInt b l[p] i + simpleRootCoeffInt b l[q] i ≤
        simpleRootCoeffInt b β i := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg
        (s := ({p, q} : Finset (Fin l.length))) (t := Finset.univ)
        (by simp) (fun x _ _ => simpleRootCoeffInt_occurrence_nonneg b l hpos x i)
        (f := fun x => simpleRootCoeffInt b l[x] i)
      rw [simpleRootCoeffInt_occurrence_sum b l β hsum i] at h
      simpa [hpq] using h
    rcases hβ i with hz | ho <;> omega
  · intro i
    constructor
    · intro hi
      change simpleRootCoeffInt b β i ≠ 0 at hi
      by_contra hn
      push Not at hn
      have hz : ∀ p : Fin l.length, simpleRootCoeffInt b l[p] i = 0 := by
        intro p
        by_contra hp
        exact hn p hp
      have hsum' := simpleRootCoeffInt_occurrence_sum b l β hsum i
      have hzero : (∑ p : Fin l.length, simpleRootCoeffInt b l[p] i) = 0 := by
        apply Finset.sum_eq_zero
        intro p _
        exact hz p
      exact hi (hsum'.symm.trans hzero)
    · rintro ⟨p, hp⟩
      change simpleRootCoeffInt b l[p] i ≠ 0 at hp
      change simpleRootCoeffInt b β i ≠ 0
      have hle : simpleRootCoeffInt b l[p] i ≤ simpleRootCoeffInt b β i := by
        rw [← simpleRootCoeffInt_occurrence_sum b l β hsum i]
        exact Finset.single_le_sum
          (fun q _ => simpleRootCoeffInt_occurrence_nonneg b l hpos q i)
          (Finset.mem_univ p)
      have hge := simpleRootCoeffInt_occurrence_nonneg b l hpos p i
      omega

end ReductiveGroups
