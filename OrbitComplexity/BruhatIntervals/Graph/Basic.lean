import OrbitComplexity.BruhatIntervals.Realizations.Reflections
import OrbitComplexity.BruhatIntervals.Order.Interval
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The labelled Bruhat graph and interval spans

The undirected Bruhat graph joins vertices differing by a reflection. Its labels are the unique
positive roots of those reflections. Restricting the graph to a Bruhat interval gives a finite
set of edge labels and hence a finite-dimensional span.

## Main definitions

* `bruhatGraph`: the undirected reflection graph of a Coxeter system.
* `edgeLabel`: the positive-root label of an edge.
* `intervalGraph`: the induced graph on a Bruhat interval.
* `labelSpan`: the real span of all edge labels in an interval.
* `algebraicDim`: the dimension of the interval label span.
* `IsToricInterval`: equality between algebraic dimension and interval length.

## Main results

* `edgeLabel_symm`: the root label does not depend on the orientation of its edge.
* `labelSpan_eq_ordered`: upward-oriented edges span the same space as all edges.
* `labelSpan_finiteDimensional`: every interval label span is finite-dimensional.

## Implementation notes

The graph is independent of the chosen realization, while its labels and their spans use that
realization. Interval finiteness suffices; neither the Coxeter group nor its simple index type
is required to be finite.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.1 and 4.4.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W) [AddCommGroup V] [Module ℝ V]

/-- The undirected Bruhat graph joins vertices differing by a Coxeter reflection. -/
def bruhatGraph : SimpleGraph W where
  Adj x y := cs.IsReflection (y * x⁻¹)
  symm := by
    constructor
    intro x y h
    have hi := h.isReflection_inv
    simpa only [mul_inv_rev, inv_inv] using hi
  loopless := by
    constructor
    intro x h
    change cs.IsReflection (x * x⁻¹) at h
    rw [mul_inv_cancel] at h
    obtain ⟨k, hk⟩ := h.odd_length
    rw [cs.length_one] at hk
    omega

variable {cs} (realization : Realization cs (V := V))

private noncomputable def edgeRoot (x y : W) (h : (bruhatGraph cs).Adj x y) :
    {root : V // root ∈ realization.positiveRoots} :=
  realization.rootReflectionEquiv.symm ⟨y * x⁻¹, h⟩

/-- The positive-root label of an edge of the Bruhat graph. -/
noncomputable def edgeLabel (x y : W) (h : (bruhatGraph cs).Adj x y) : V :=
  (edgeRoot realization x y h).val

/-- Every edge label is a positive root. -/
theorem edgeLabel_positive (x y : W) (h : (bruhatGraph cs).Adj x y) :
    edgeLabel realization x y h ∈ realization.positiveRoots :=
  (edgeRoot realization x y h).property

private theorem edgeRoot_reflection (x y : W) (h : (bruhatGraph cs).Adj x y) :
    (realization.rootReflection (edgeRoot realization x y h)).val = y * x⁻¹ := by
  have href := realization.rootReflectionEquiv.apply_symm_apply ⟨y * x⁻¹, h⟩
  exact congrArg Subtype.val href

/-- The reflection in an edge label carries its first endpoint to its second. -/
theorem edgeLabel_target (x y : W) (h : (bruhatGraph cs).Adj x y) :
    y = (realization.rootReflection
      ⟨edgeLabel realization x y h, edgeLabel_positive realization x y h⟩).val * x := by
  change y = (realization.rootReflection (edgeRoot realization x y h)).val * x
  rw [edgeRoot_reflection]
  group

/-- Reversing an undirected edge preserves its positive-root label. -/
theorem edgeLabel_symm (x y : W) (h : (bruhatGraph cs).Adj x y) :
    edgeLabel realization x y h = edgeLabel realization y x ((bruhatGraph cs).adj_symm h) := by
  have hreflect : y * x⁻¹ = x * y⁻¹ := by
    calc
      y * x⁻¹ = (y * x⁻¹)⁻¹ := h.inv.symm
      _ = x * y⁻¹ := by group
  have hsub : (⟨y * x⁻¹, h⟩ : {t : W // cs.IsReflection t}) =
      ⟨x * y⁻¹, (bruhatGraph cs).adj_symm h⟩ := Subtype.ext hreflect
  exact congrArg (fun t => (realization.rootReflectionEquiv.symm t).val) hsub

/-- Two vertices are adjacent exactly when a positive-root reflection joins them. -/
theorem bruhatGraph_adj_iff (x y : W) :
    (bruhatGraph cs).Adj x y ↔
      ∃ root : {α : V // α ∈ realization.positiveRoots},
        y = (realization.rootReflection root).val * x := by
  constructor
  · intro h
    exact ⟨edgeRoot realization x y h, edgeLabel_target realization x y h⟩
  · rintro ⟨root, rfl⟩
    change cs.IsReflection ((realization.rootReflection root).val * x * x⁻¹)
    simpa only [mul_inv_cancel_right] using (realization.rootReflection root).property

/-- An edge has a unique positive-root label realizing its reflection. -/
theorem edgeLabel_unique {x y : W} (h : (bruhatGraph cs).Adj x y)
    (root : {α : V // α ∈ realization.positiveRoots})
    (htarget : y = (realization.rootReflection root).val * x) :
    edgeLabel realization x y h = root.val := by
  have href : (realization.rootReflection (edgeRoot realization x y h)).val =
      (realization.rootReflection root).val := by
    apply mul_right_cancel (b := x)
    have hleft : y =
        (realization.rootReflection (edgeRoot realization x y h)).val * x :=
      edgeLabel_target realization x y h
    exact hleft.symm.trans htarget
  exact congrArg Subtype.val (realization.rootReflection_injective (Subtype.ext href))

/-- The induced Bruhat graph whose vertices belong to the given Bruhat interval. -/
def intervalGraph (u v : W) : SimpleGraph (bruhatInterval cs u v) :=
  (bruhatGraph cs).induce (bruhatInterval cs u v)

/-- The real span of all labels of edges within a Bruhat interval. -/
noncomputable def labelSpan (u v : W) : Submodule ℝ V :=
  Submodule.span ℝ {α : V | ∃ x ∈ bruhatInterval cs u v, ∃ y ∈ bruhatInterval cs u v,
    ∃ h : (bruhatGraph cs).Adj x y, edgeLabel realization x y h = α}

/-- The algebraic dimension is the dimension of the interval label span. -/
noncomputable def algebraicDim (u v : W) : ℕ :=
  Module.finrank ℝ (labelSpan realization u v)

/-- A Bruhat interval is toric when its algebraic dimension equals its length. -/
def IsToricInterval (u v : W) : Prop :=
  algebraicDim realization u v = cs.length v - cs.length u

/-- Directed Bruhat steps are adjacent pairs of increasing length. -/
theorem bruhatStep_iff_adj {x y : W} :
    cs.BruhatStep x y ↔ (bruhatGraph cs).Adj x y ∧ cs.length x < cs.length y := by
  constructor
  · rintro ⟨t, ht, htarget, hlt⟩
    refine ⟨?_, hlt⟩
    change cs.IsReflection (y * x⁻¹)
    rw [htarget, mul_inv_cancel_right]
    exact ht
  · rintro ⟨h, hlt⟩
    refine ⟨y * x⁻¹, h, ?_, hlt⟩
    group

/-- Adjacent Bruhat vertices have different Coxeter lengths. -/
theorem bruhatGraph_adj_length_ne {x y : W} (h : (bruhatGraph cs).Adj x y) :
    cs.length x ≠ cs.length y := by
  have hne := h.length_mul_right_ne x
  simpa only [mul_assoc, inv_mul_cancel, mul_one, ne_eq, eq_comm] using hne

private theorem edgeLabels_finite (u v : W) :
    {α : V | ∃ x ∈ bruhatInterval cs u v, ∃ y ∈ bruhatInterval cs u v,
      ∃ h : (bruhatGraph cs).Adj x y, edgeLabel realization x y h = α}.Finite := by
  classical
  let label : W × W → V := fun pair =>
    if h : (bruhatGraph cs).Adj pair.1 pair.2 then edgeLabel realization pair.1 pair.2 h else 0
  refine (((bruhatInterval_finite cs u v).prod
    (bruhatInterval_finite cs u v)).image label).subset ?_
  rintro α ⟨x, hx, y, hy, hxy, hlabel⟩
  refine ⟨(x, y), ⟨hx, hy⟩, ?_⟩
  simpa only [label, dite_eq_left hxy] using hlabel

/-- Every interval label span is finite-dimensional. -/
instance labelSpan_finiteDimensional (u v : W) :
    FiniteDimensional ℝ (labelSpan realization u v) :=
  FiniteDimensional.span_of_finite ℝ (edgeLabels_finite realization u v)

/-- Upward-oriented interval edges span the same space as all interval edges. -/
theorem labelSpan_eq_ordered (u v : W) :
    labelSpan realization u v = Submodule.span ℝ
      {α : V | ∃ x y : W, cs.BruhatLE u x ∧ cs.BruhatLE y v ∧
        ∃ h : (bruhatGraph cs).Adj x y, cs.length x < cs.length y ∧
          edgeLabel realization x y h = α} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro α ⟨x, hx, y, hy, hxy, hlabel⟩
    apply Submodule.subset_span
    rcases lt_or_gt_of_ne (bruhatGraph_adj_length_ne hxy) with hlt | hgt
    · exact ⟨x, y, hx.1, hy.2, hxy, hlt, hlabel⟩
    · refine ⟨y, x, hy.1, hx.2, (bruhatGraph cs).adj_symm hxy, hgt, ?_⟩
      exact (edgeLabel_symm realization x y hxy).symm.trans hlabel
  · apply Submodule.span_le.mpr
    rintro α ⟨x, y, hux, hyv, hxy, hlt, hlabel⟩
    have hle : cs.BruhatLE x y :=
      Relation.ReflTransGen.single (bruhatStep_iff_adj.mpr ⟨hxy, hlt⟩)
    exact Submodule.subset_span ⟨x, ⟨hux, hle.trans hyv⟩, y, ⟨hux.trans hle, hyv⟩, hxy, hlabel⟩

/-- The undirected Bruhat graph, its positive symmetric labels, and its interval restriction
satisfy their defining properties. -/
theorem bruhat_graph_definitions :
    ∀ {S W V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
      [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V)) (u v : W),
      cs.BruhatLE u v →
      (∀ x y : W, (bruhatGraph cs).Adj x y ↔
        ∃ root : {α : V // α ∈ realization.positiveRoots},
          y = (realization.rootReflection root).val * x) ∧
      (∀ (x y : W) (h : (bruhatGraph cs).Adj x y),
        edgeLabel realization x y h ∈ realization.positiveRoots ∧
        y = (realization.rootReflection
          ⟨edgeLabel realization x y h, edgeLabel_positive realization x y h⟩).val * x ∧
        edgeLabel realization x y h =
          edgeLabel realization y x ((bruhatGraph cs).adj_symm h)) ∧
      (∀ x y : bruhatInterval cs u v,
        (intervalGraph (cs := cs) u v).Adj x y ↔ (bruhatGraph cs).Adj x.val y.val) := by
  intro S W V _ M cs _ _ realization u v _huv
  refine ⟨bruhatGraph_adj_iff realization, ?_, ?_⟩
  · intro x y h
    exact ⟨edgeLabel_positive realization x y h, edgeLabel_target realization x y h,
      edgeLabel_symm realization x y h⟩
  · intro x y
    rfl

/-- The all-edge and upward-edge spans coincide, are finite-dimensional, and define the
algebraic dimension by their real dimension. -/
theorem algebraic_dim_definitions :
    ∀ {S W V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
      [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V)) (u v : W),
      cs.BruhatLE u v →
      labelSpan realization u v = Submodule.span ℝ
        {α : V | ∃ x ∈ bruhatInterval cs u v, ∃ y ∈ bruhatInterval cs u v,
          ∃ h : (bruhatGraph cs).Adj x y, edgeLabel realization x y h = α} ∧
      labelSpan realization u v = Submodule.span ℝ
        {α : V | ∃ x y : W, cs.BruhatLE u x ∧ cs.BruhatLE y v ∧
          ∃ h : (bruhatGraph cs).Adj x y, cs.length x < cs.length y ∧
            edgeLabel realization x y h = α} ∧
      FiniteDimensional ℝ (labelSpan realization u v) ∧
      algebraicDim realization u v = Module.finrank ℝ (labelSpan realization u v) := by
  intro S W V _ M cs _ _ realization u v _huv
  exact ⟨rfl, labelSpan_eq_ordered realization u v, inferInstance, rfl⟩

/-- A Bruhat interval is toric exactly when its algebraic dimension equals its length. -/
theorem isToricInterval_iff :
    ∀ {S W V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
      [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V)) (u v : W),
      cs.BruhatLE u v →
      (IsToricInterval realization u v ↔
        algebraicDim realization u v = cs.length v - cs.length u) := by
  intro S W V _ M cs _ _ realization u v _huv
  rfl

end BruhatIntervals
