import OrbitComplexity.BruhatIntervals.Graph.Chains
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimension of interval label spans

The labels on a saturated endpoint chain span the interval label space. There is one such label
per unit of Coxeter-length difference, so algebraic dimension is bounded by interval length.

## Main results

* `algebraicDim_le_length`: algebraic dimension is at most the interval's length.
* `toric_interval_definition`: the dimension bound and the defining toric equality.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.2.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

/-- The dimension of an interval's label span is at most its Coxeter-length difference. -/
theorem algebraicDim_le_length (u v : W) (huv : cs.BruhatLE u v) :
    algebraicDim realization u v ≤ cs.length v - cs.length u := by
  classical
  obtain ⟨vertices, hhead, hlast, hchain, hlength⟩ := exists_bruhat_chain cs u v huv
  let pairs := vertices.zip vertices.tail
  let label : W × W → V := fun pair =>
    if h : (bruhatGraph cs).Adj pair.1 pair.2 then
      edgeLabel realization pair.1 pair.2 h else 0
  let labels : Fin pairs.length → V := fun j => label (pairs.get j)
  have hspan : labelSpan realization u v ≤ Submodule.span ℝ (Set.range labels) := by
    rw [(labelSpan_properties realization u v huv).2.1 vertices hhead hlast hchain]
    apply Submodule.span_le.mpr
    rintro α ⟨x, y, hp, h, hlabel⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
    apply Submodule.subset_span
    refine ⟨j, ?_⟩
    dsimp only [labels]
    rw [hj]
    simpa only [label, dite_eq_left h] using hlabel
  have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range labels)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range labels)
  have hdim : algebraicDim realization u v ≤ pairs.length :=
    (Submodule.finrank_mono hspan).trans (by
      simpa only [Set.finrank, Fintype.card_fin] using finrank_range_le_card (R := ℝ) labels)
  have hpairs : pairs.length = cs.length v - cs.length u := by
    dsimp only [pairs]
    rw [List.length_zip, List.length_tail, Nat.min_eq_right (Nat.sub_le _ _), hlength]
    omega
  exact hpairs ▸ hdim

/-- Every interval obeys the dimension bound, and it is toric exactly when equality holds. -/
theorem toric_interval_definition (u v : W) (huv : cs.BruhatLE u v) :
    algebraicDim realization u v ≤ cs.length v - cs.length u ∧
      (IsToricInterval realization u v ↔
        algebraicDim realization u v = cs.length v - cs.length u) := by
  exact ⟨algebraicDim_le_length realization u v huv,
    isToricInterval_iff cs realization u v huv⟩

end BruhatIntervals

