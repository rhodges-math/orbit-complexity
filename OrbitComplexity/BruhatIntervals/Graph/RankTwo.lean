import OrbitComplexity.BruhatIntervals.Words.RankTwo
import OrbitComplexity.BruhatIntervals.Graph.ThinIntervals

/-!
# Long edges in rank-two Bruhat graphs

Opposite length parity gives all rank-two reflection edges. A saturated three-cover segment,
together with the other middle vertex in each of its two diamonds, gives four intermediate
vertices with every adjacency between successive levels.

## Main results

* `rankTwo_long_edge_fork`: a long directed rank-two edge has the four-vertex intermediate fork.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991),
  Example 1.2 and the proof of Proposition 3.3.
-/

namespace BruhatIntervals

variable {W : Type*} [Group W] {M : CoxeterMatrix Bool} (cs : CoxeterSystem M W)

/-- A long directed edge in a rank-two Bruhat graph has two distinct vertices on each of two
intermediate levels, with all eight adjacencies between successive levels. -/
theorem rankTwo_long_edge_fork (x y : W) (hxy : cs.BruhatStep x y)
    (hgap : cs.length x + 1 < cs.length y) :
    ∃ a b c d : W, a ∈ bruhatInterval cs x y ∧ b ∈ bruhatInterval cs x y ∧
      c ∈ bruhatInterval cs x y ∧ d ∈ bruhatInterval cs x y ∧ a ≠ b ∧ c ≠ d ∧
      (bruhatGraph cs).Adj x a ∧ (bruhatGraph cs).Adj x b ∧
      (bruhatGraph cs).Adj a c ∧ (bruhatGraph cs).Adj a d ∧
      (bruhatGraph cs).Adj b c ∧ (bruhatGraph cs).Adj b d ∧
      (bruhatGraph cs).Adj c y ∧ (bruhatGraph cs).Adj d y := by
  let : PartialOrder W := cs.bruhatPartialOrder
  have hodd := (rankTwo_adj_iff cs x y).mp (bruhatStep_iff_adj.mp hxy).1
  have hmod := Nat.odd_iff.mp hodd
  have hgap3 : cs.length x + 3 ≤ cs.length y := by omega
  obtain ⟨a, hxa, hay⟩ := exists_bruhat_covBy_le cs hxy.bruhatLE
    (by intro heq; have := hxy.length_lt; rw [heq] at this; omega)
  have hla := ((bruhat_covBy_iff cs x a).mp hxa).2
  obtain ⟨c, hac, hcy⟩ := exists_bruhat_covBy_le cs hay
    (by intro heq; rw [heq] at hla; omega)
  have hlc := ((bruhat_covBy_iff cs a c).mp hac).2
  obtain ⟨last, hcl, hly⟩ := exists_bruhat_covBy_le cs hcy
    (by intro heq; rw [heq] at hlc; omega)
  obtain ⟨b, ⟨hba, hxb, hbc⟩, _⟩ := bruhat_rank_two_diamond cs x a c hxa hac
  obtain ⟨d, ⟨hdc, had, hdl⟩, _⟩ := bruhat_rank_two_diamond cs a c last hac hcl
  have hlb := ((bruhat_covBy_iff cs x b).mp hxb).2
  have hld := ((bruhat_covBy_iff cs a d).mp had).2
  have edge {p q : W} (h : p ⋖ q) : (bruhatGraph cs).Adj p q :=
    (bruhatStep_iff_adj.mp (bruhat_covBy_step cs h)).1
  refine ⟨a, b, c, d, ⟨hxa.le, hay⟩, ⟨hxb.le, hbc.le.trans hcy⟩,
    ⟨hxa.le.trans hac.le, hcy⟩, ⟨hxa.le.trans had.le, hdl.le.trans hly⟩,
    hba.symm, hdc.symm, edge hxa, edge hxb, edge hac, edge had, edge hbc, ?_, ?_, ?_⟩
  · apply (rankTwo_adj_iff cs b d).mpr
    rw [Nat.odd_iff]
    omega
  · apply (rankTwo_adj_iff cs c y).mpr
    rw [Nat.odd_iff]
    omega
  · apply (rankTwo_adj_iff cs d y).mpr
    rw [Nat.odd_iff]
    omega

end BruhatIntervals
