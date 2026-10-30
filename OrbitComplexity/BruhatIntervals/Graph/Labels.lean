import OrbitComplexity.BruhatIntervals.Graph.Basic

/-!
# Transport and containment of interval labels

Right multiplication preserves Bruhat edge labels. Inclusion of intervals preserves their label
spans, and a singleton interval has zero label span.

## Main results

* `bruhatGraph_adj_mul_right`: right multiplication preserves graph adjacency.
* `edgeLabel_mul_right`: right multiplication preserves positive-root labels.
* `labelSpan_mono`: inclusion of intervals gives inclusion of label spans.
* `labelSpan_self`: a singleton interval has zero span.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.1 and 4.4.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]

/-- Simultaneous right multiplication preserves adjacency in the reflection graph. -/
theorem bruhatGraph_adj_mul_right (x y g : W) :
    (bruhatGraph cs).Adj (x * g) (y * g) ↔ (bruhatGraph cs).Adj x y := by
  change cs.IsReflection (y * g * (x * g)⁻¹) ↔ cs.IsReflection (y * x⁻¹)
  have heq : y * g * (x * g)⁻¹ = y * x⁻¹ := by group
  rw [heq]

variable (realization : Realization cs (V := V))

/-- Simultaneous right multiplication preserves the positive-root label of an edge. -/
theorem edgeLabel_mul_right (x y : W) (h : (bruhatGraph cs).Adj x y) (g : W) :
    edgeLabel realization (x * g) (y * g) ((bruhatGraph_adj_mul_right x y g).mpr h) =
      edgeLabel realization x y h := by
  apply edgeLabel_unique realization _
    ⟨edgeLabel realization x y h, edgeLabel_positive realization x y h⟩
  have htarget := congrArg (· * g) (edgeLabel_target realization x y h)
  simpa only [mul_assoc] using htarget

/-- Enlarging the endpoints of an interval enlarges its label span. -/
theorem labelSpan_mono {u v u' v' : W}
    (hlower : cs.BruhatLE u' u) (hupper : cs.BruhatLE v v') :
    labelSpan realization u v ≤ labelSpan realization u' v' := by
  apply Submodule.span_le.mpr
  rintro α ⟨x, hx, y, hy, hxy, hlabel⟩
  exact Submodule.subset_span
    ⟨x, ⟨hlower.trans hx.1, hx.2.trans hupper⟩,
      y, ⟨hlower.trans hy.1, hy.2.trans hupper⟩, hxy, hlabel⟩

/-- A singleton Bruhat interval has no edges and hence has zero label span. -/
theorem labelSpan_self (w : W) : labelSpan realization w w = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro α ⟨x, hx, y, hy, hxy, _⟩
  have hxw : x = w := hx.2.antisymm hx.1
  have hyw : y = w := hy.2.antisymm hy.1
  exact ((bruhatGraph cs).ne_of_adj hxy (hxw.trans hyw.symm)).elim

end BruhatIntervals

