import OrbitComplexity.BruhatIntervals.Words.Parabolic
import OrbitComplexity.BruhatIntervals.Order.Basic

/-!
# Parabolic factors and left descents

Length additivity identifies a product's parabolic left descents with those of its parabolic
factor. A factor has every such descent exactly when it is the greatest element of its
standard parabolic subgroup in Bruhat order.

## Main results

* `isLeftDescent_parabolic_iff`: the parabolic factor and product have the same indexed descents.
* `parabolic_greatest_iff_descents`: all indexed descents characterize the greatest factor.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.2 and 2.4.
-/

namespace BruhatIntervals

universe u v

variable {Index : Type u} {W : Type v} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

private theorem word_le_of_left_descents {indices : Set Index} {a : W}
    (hdescents : ∀ i ∈ indices, cs.IsLeftDescent a i) (word : List Index) :
    (∀ i ∈ word, i ∈ indices) → cs.BruhatLE (cs.wordProd word) a := by
  induction word with
  | nil =>
    intro _
    exact cs.one_bruhatLE a
  | cons i word ih =>
    intro hletters
    have htail : cs.BruhatLE (cs.wordProd word) a :=
      ih fun j hj => hletters j (List.mem_cons_of_mem i hj)
    have hi : cs.IsLeftDescent a i := hdescents i (hletters i (List.mem_cons_self))
    have hright : cs.IsRightDescent a⁻¹ i := cs.isRightDescent_inv_iff.mpr hi
    have hstep := (htail.inv.mul_simple_of_isRightDescent i hright).inv
    simpa only [mul_inv_rev, cs.inv_simple, inv_inv, cs.wordProd_cons] using hstep

/-- A parabolic-prefix factor and its product with a minimal left representative have the
same left descents among the parabolic indices. -/
theorem isLeftDescent_parabolic_iff {indices : Set Index} {a d : W}
    (ha : a ∈ cs.parabolic indices) (hd : IsMinimalLeftRep cs indices d)
    {i : Index} (hi : i ∈ indices) :
    cs.IsLeftDescent (a * d) i ↔ cs.IsLeftDescent a i := by
  have hproduct : cs.length (a * d) = cs.length a + cs.length d :=
    cs.length_mul_of_forall_not_isLeftDescent ha ((isMinimalLeftRep_iff cs).mp hd)
  have hparabolic : cs.simple i * a ∈ cs.parabolic indices :=
    (cs.parabolic indices).mul_mem (cs.simple_mem_parabolic hi) ha
  have hstep : cs.length (cs.simple i * a * d) =
      cs.length (cs.simple i * a) + cs.length d :=
    cs.length_mul_of_forall_not_isLeftDescent hparabolic ((isMinimalLeftRep_iff cs).mp hd)
  change cs.length (cs.simple i * (a * d)) < cs.length (a * d) ↔
    cs.length (cs.simple i * a) < cs.length a
  rw [← mul_assoc, hstep, hproduct, Nat.add_lt_add_iff_right]

/-- Every parabolic index is a left descent of the product exactly when its parabolic
factor is the greatest element of the standard parabolic subgroup in Bruhat order. -/
theorem parabolic_greatest_iff_descents {indices : Set Index} {a d : W}
    (ha : a ∈ cs.parabolic indices) (hd : IsMinimalLeftRep cs indices d) :
    let : PartialOrder W := cs.bruhatPartialOrder
    (∀ i ∈ indices, cs.IsLeftDescent (a * d) i) ↔
      IsGreatest (cs.parabolic indices : Set W) a := by
  let : PartialOrder W := cs.bruhatPartialOrder
  constructor
  · intro hdescents
    refine ⟨ha, ?_⟩
    intro p hp
    change cs.BruhatLE p a
    obtain ⟨word, hletters, hproduct⟩ := cs.exists_wordProd_eq_of_mem_parabolic hp
    rw [← hproduct]
    apply word_le_of_left_descents cs ?_ word hletters
    intro i hi
    exact (isLeftDescent_parabolic_iff cs ha hd hi).mp (hdescents i hi)
  · intro hgreatest i hi
    apply (isLeftDescent_parabolic_iff cs ha hd hi).mpr
    by_contra hnot
    have hparabolic : cs.simple i * a ∈ cs.parabolic indices :=
      (cs.parabolic indices).mul_mem (cs.simple_mem_parabolic hi) ha
    have hbelow : cs.BruhatLE (cs.simple i * a) a := hgreatest.2 hparabolic
    have hbound := hbelow.length_le
    have hlength := cs.not_isLeftDescent_iff.mp hnot
    omega

end BruhatIntervals
