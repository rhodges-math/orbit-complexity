import TauCeti.GroupTheory.Coxeter.Parabolic

/-!
# Length-additive parabolic decompositions

Every Coxeter group element factors uniquely into a minimal coset representative and an element
of a standard parabolic subgroup, on either side. Both factorizations add Coxeter lengths.

## Main definitions

* `IsMinimalLeftRep`: minimal length in a left parabolic coset.

## Main results

* `right_parabolic_decomposition`: unique right parabolic factorization and length additivity.
* `left_parabolic_decomposition`: unique left parabolic factorization and length additivity.
* `isMinimalLeftRep_iff`: minimality is equivalent to absence of left descents in the indices.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.4.
-/

namespace BruhatIntervals

variable {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

/-- A left parabolic representative has minimal length among its left translates by the
parabolic subgroup. -/
def IsMinimalLeftRep (indices : Set S) (w : W) : Prop :=
  ∀ a ∈ cs.parabolic indices, cs.length w ≤ cs.length (a * w)

/-- A representative is minimal in its left parabolic coset exactly when it has no left descent
among the parabolic indices. -/
theorem isMinimalLeftRep_iff {indices : Set S} {w : W} :
    IsMinimalLeftRep cs indices w ↔ ∀ i ∈ indices, ¬ cs.IsLeftDescent w i := by
  constructor
  · intro h i hi hdesc
    exact (Nat.not_lt_of_ge (h _ (cs.simple_mem_parabolic hi))) hdesc
  · intro h a ha
    rw [cs.length_mul_of_forall_not_isLeftDescent ha h]
    exact Nat.le_add_left _ _

/-- Each element has a unique factorization as a minimal right parabolic representative times
a parabolic element, and the lengths of the factors add to its length. -/
theorem right_parabolic_decomposition (indices : Set S) (w : W) :
    ∃! factors : W × W, cs.IsMinimalCosetRep indices factors.1 ∧
      factors.2 ∈ cs.parabolic indices ∧ w = factors.1 * factors.2 ∧
      cs.length w = cs.length factors.1 + cs.length factors.2 := by
  obtain ⟨factors, h, huniq⟩ := cs.existsUnique_isMinimalCosetRep_mul indices w
  refine ⟨factors, ⟨h.1, h.2.1, h.2.2, ?_⟩, ?_⟩
  · rw [h.2.2]
    exact cs.length_mul_of_isMinimalCosetRep h.1 h.2.1
  · intro other hother
    exact huniq other ⟨hother.1, hother.2.1, hother.2.2.1⟩

/-- Each element has a unique factorization as a parabolic element times a representative with
no left descent in the parabolic indices, and the lengths of the factors add to its length. -/
theorem left_parabolic_decomposition (indices : Set S) (w : W) :
    ∃! factors : W × W, factors.1 ∈ cs.parabolic indices ∧
      (∀ i ∈ indices, ¬ cs.IsLeftDescent factors.2 i) ∧
      w = factors.1 * factors.2 ∧
      cs.length w = cs.length factors.1 + cs.length factors.2 := by
  obtain ⟨factors, h, huniq⟩ := cs.existsUnique_mem_parabolic_mul indices w
  refine ⟨factors, ⟨h.1, h.2.1, h.2.2, ?_⟩, ?_⟩
  · rw [h.2.2]
    exact cs.length_mul_of_forall_not_isLeftDescent h.1 h.2.1
  · intro other hother
    exact huniq other ⟨hother.1, hother.2.1, hother.2.2.1⟩

end BruhatIntervals
