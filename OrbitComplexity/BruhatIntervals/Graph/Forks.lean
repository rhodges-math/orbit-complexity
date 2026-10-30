import OrbitComplexity.BruhatIntervals.Graph.PathSystem
import OrbitComplexity.BruhatIntervals.Graph.RankTwo
import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.Graphs

/-!
# Four-vertex refinements of long Bruhat edges

A directed three-edge refinement generates a canonical dihedral subsystem. Translate its right
coset by a minimum-length representative, construct the two intermediate levels in the
rank-two graph, and translate them back. The resulting four vertices lie in the original
interval and have every adjacency between successive levels.

## Main results

* `long_edge_fork`: every long directed Bruhat edge has a four-vertex intermediate fork.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991),
  Theorem 1.4, Example 1.2, and the proof of Proposition 3.3.
-/

namespace BruhatIntervals

variable {Index W : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

private theorem coset_fork (H : Subgroup W) {M : CoxeterMatrix Bool}
    (system : CoxeterSystem M H)
    (hcanonical : ∀ i, (system.simple i).val ∈ canonicalReflections cs H)
    (z : W) (hz : ∀ t ∈ H, ¬cs.IsLeftInversion z t) (x y : H)
    (hxy : system.BruhatStep x y) (hgap : system.length x + 1 < system.length y) :
    ∃ a b c d : W,
      a ∈ bruhatInterval cs (x.val * z) (y.val * z) ∧
      b ∈ bruhatInterval cs (x.val * z) (y.val * z) ∧
      c ∈ bruhatInterval cs (x.val * z) (y.val * z) ∧
      d ∈ bruhatInterval cs (x.val * z) (y.val * z) ∧ a ≠ b ∧ c ≠ d ∧
      (bruhatGraph cs).Adj (x.val * z) a ∧ (bruhatGraph cs).Adj (x.val * z) b ∧
      (bruhatGraph cs).Adj a c ∧ (bruhatGraph cs).Adj a d ∧
      (bruhatGraph cs).Adj b c ∧ (bruhatGraph cs).Adj b d ∧
      (bruhatGraph cs).Adj c (y.val * z) ∧ (bruhatGraph cs).Adj d (y.val * z) := by
  have stepMap {h k : H} (hedge : system.BruhatStep h k) :
      cs.BruhatStep (h.val * z) (k.val * z) :=
    (bruhatStep_mul_coset_iff cs H z hz h.property k.property).mpr
      ((canonical_bruhatStep_iff cs H system hcanonical h k).mp hedge)
  have orderMap {h k : H} (hle : system.BruhatLE h k) :
      cs.BruhatLE (h.val * z) (k.val * z) := by
    induction hle with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hedge ih => exact ih.tail (stepMap hedge)
  have adjMap {h k : H} (hedge : (bruhatGraph system).Adj h k) :
      (bruhatGraph cs).Adj (h.val * z) (k.val * z) := by
    rcases lt_or_gt_of_ne (bruhatGraph_adj_length_ne hedge) with hlt | hgt
    · exact (bruhatStep_iff_adj.mp (stepMap (bruhatStep_iff_adj.mpr ⟨hedge, hlt⟩))).1
    · exact (bruhatGraph cs).adj_symm
        (bruhatStep_iff_adj.mp (stepMap (bruhatStep_iff_adj.mpr
          ⟨(bruhatGraph system).adj_symm hedge, hgt⟩))).1
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hcd,
    hxa, hxb, hac, had, hbc, hbd, hcy, hdy⟩ := rankTwo_long_edge_fork system x y hxy hgap
  refine ⟨a.val * z, b.val * z, c.val * z, d.val * z,
    ⟨orderMap ha.1, orderMap ha.2⟩, ⟨orderMap hb.1, orderMap hb.2⟩,
    ⟨orderMap hc.1, orderMap hc.2⟩, ⟨orderMap hd.1, orderMap hd.2⟩,
    ?_, ?_, adjMap hxa, adjMap hxb, adjMap hac, adjMap had,
    adjMap hbc, adjMap hbd, adjMap hcy, adjMap hdy⟩
  · intro heq
    exact hab (Subtype.ext (mul_right_cancel heq))
  · intro heq
    exact hcd (Subtype.ext (mul_right_cancel heq))

/-- Every long directed Bruhat edge has two distinct vertices on each of two intermediate
levels, lying in its interval and satisfying all eight successive-level adjacencies. -/
theorem long_edge_fork (x y : W) (hxy : cs.BruhatStep x y)
    (hgap : cs.length x + 1 < cs.length y) :
    ∃ a b c d : W, a ∈ bruhatInterval cs x y ∧ b ∈ bruhatInterval cs x y ∧
      c ∈ bruhatInterval cs x y ∧ d ∈ bruhatInterval cs x y ∧ a ≠ b ∧ c ≠ d ∧
      (bruhatGraph cs).Adj x a ∧ (bruhatGraph cs).Adj x b ∧
      (bruhatGraph cs).Adj a c ∧ (bruhatGraph cs).Adj a d ∧
      (bruhatGraph cs).Adj b c ∧ (bruhatGraph cs).Adj b d ∧
      (bruhatGraph cs).Adj c y ∧ (bruhatGraph cs).Adj d y := by
  obtain ⟨a, b, hfirst, hmiddle, hlast, _⟩ := long_edge_path cs x y hxy hgap
  let H := Subgroup.closure ({a * x⁻¹, b * a⁻¹, y * b⁻¹} : Set W)
  obtain ⟨M, system, hcanonical⟩ := long_edge_subsystem cs x a b y hxy hfirst hmiddle hlast
  obtain ⟨z, hzmem, _, hz⟩ := exists_minimal_coset cs H x
  have hx : x * z⁻¹ ∈ H := by
    simpa only [mul_inv_rev, inv_inv] using H.inv_mem hzmem
  have ha : a * z⁻¹ ∈ H := by
    have h := H.mul_mem (Subgroup.subset_closure (Or.inl rfl)) hx
    convert h using 1
    group
  have hb : b * z⁻¹ ∈ H := by
    have h := H.mul_mem (Subgroup.subset_closure (Or.inr (Or.inl rfl))) ha
    convert h using 1
    group
  have hy : y * z⁻¹ ∈ H := by
    have h := H.mul_mem (Subgroup.subset_closure (Or.inr (Or.inr rfl))) hb
    convert h using 1
    group
  let xH : H := ⟨x * z⁻¹, hx⟩
  let aH : H := ⟨a * z⁻¹, ha⟩
  let bH : H := ⟨b * z⁻¹, hb⟩
  let yH : H := ⟨y * z⁻¹, hy⟩
  have stepBack {h k : H} (hedge : cs.BruhatStep (h.val * z) (k.val * z)) :
      system.BruhatStep h k :=
    (canonical_bruhatStep_iff cs H system hcanonical h k).mpr
      ((bruhatStep_mul_coset_iff cs H z hz h.property k.property).mp hedge)
  have hfirst' : system.BruhatStep xH aH := stepBack
    (by simpa only [xH, aH, inv_mul_cancel_right] using hfirst)
  have hmiddle' : system.BruhatStep aH bH := stepBack
    (by simpa only [aH, bH, inv_mul_cancel_right] using hmiddle)
  have hlast' : system.BruhatStep bH yH := stepBack
    (by simpa only [bH, yH, inv_mul_cancel_right] using hlast)
  have hxy' : system.BruhatStep xH yH := stepBack
    (by simpa only [xH, yH, inv_mul_cancel_right] using hxy)
  have hgap' : system.length xH + 1 < system.length yH := by
    have := hfirst'.length_lt
    have := hmiddle'.length_lt
    have := hlast'.length_lt
    omega
  have hfork := coset_fork cs H system hcanonical z hz xH yH hxy' hgap'
  simpa only [xH, yH, inv_mul_cancel_right] using hfork

end BruhatIntervals
