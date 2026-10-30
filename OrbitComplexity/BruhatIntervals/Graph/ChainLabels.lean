import OrbitComplexity.BruhatIntervals.Graph.Basic
import Mathlib.Data.List.Chain

/-!
# Label spans of vertex lists

The consecutive edge labels of a vertex list generate its chain-label span. Appending one edge
adds its label line, and joining lists at a shared endpoint adds their spans.

## Main definitions

* `chainLabelSpan`: the span of positive-root labels on consecutive adjacent vertices.

## Main results

* `chainLabelSpan_snoc`: adjoining a last edge adds its label line.
* `chainLabelSpan_overlap`: joining lists at one vertex adds their spans.
* `chainLabelSpan_singleton`: a one-vertex list has no labels.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.2.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private theorem zip_tail_snoc {α : Type*} (vertices : List α) (last next : α)
    (hlast : vertices.getLast? = some last) :
    (vertices ++ [next]).zip (vertices ++ [next]).tail =
      vertices.zip vertices.tail ++ [(last, next)] := by
  induction vertices with
  | nil => simp at hlast
  | cons first rest ih =>
    cases rest with
    | nil =>
      have heq : first = last := Option.some.inj hlast
      subst first
      rfl
    | cons second rest =>
      simp only [List.cons_append, List.tail_cons, List.zip_cons_cons]
      apply congrArg ((first, second) :: ·)
      exact ih (by simpa only [List.getLast?_cons_cons] using hlast)


private noncomputable def pairSpan (pairs : List (W × W)) : Submodule ℝ V :=
  Submodule.span ℝ {α : V | ∃ x y : W, (x, y) ∈ pairs ∧
    ∃ h : (bruhatGraph cs).Adj x y, edgeLabel realization x y h = α}

/-- The span of the positive-root labels on consecutive edges of a vertex list. -/
noncomputable def chainLabelSpan (vertices : List W) : Submodule ℝ V :=
  pairSpan realization (vertices.zip vertices.tail)

/-- A one-vertex list has no consecutive edges and hence zero chain-label span. -/
theorem chainLabelSpan_singleton (w : W) : chainLabelSpan realization [w] = ⊥ := by
  simp [chainLabelSpan, pairSpan]

private theorem pairSpan_append (first second : List (W × W)) :
    pairSpan realization (first ++ second) = pairSpan realization first ⊔
      pairSpan realization second := by
  unfold pairSpan
  rw [← Submodule.span_union]
  congr 1
  ext α
  constructor
  · rintro ⟨x, y, hp, h, hlabel⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact Or.inl ⟨x, y, hp, h, hlabel⟩
    · exact Or.inr ⟨x, y, hp, h, hlabel⟩
  · rintro (⟨x, y, hp, h, hlabel⟩ | ⟨x, y, hp, h, hlabel⟩)
    · exact ⟨x, y, List.mem_append.mpr (Or.inl hp), h, hlabel⟩
    · exact ⟨x, y, List.mem_append.mpr (Or.inr hp), h, hlabel⟩

private theorem pairSpan_singleton (x y : W) (h : (bruhatGraph cs).Adj x y) :
    pairSpan realization [(x, y)] = ℝ ∙ edgeLabel realization x y h := by
  unfold pairSpan
  congr 1
  ext α
  constructor
  · rintro ⟨a, b, hp, h', hlabel⟩
    have hp' : (a, b) = (x, y) := List.mem_singleton.mp hp
    rcases Prod.mk.inj hp' with ⟨rfl, rfl⟩
    exact hlabel.symm
  · intro heq
    exact ⟨x, y, List.mem_singleton.mpr rfl, h, heq.symm⟩

/-- Appending one adjacent vertex adds the line of its last edge label to the chain span. -/
theorem chainLabelSpan_snoc (vertices : List W) (last next : W)
    (hlast : vertices.getLast? = some last) (h : (bruhatGraph cs).Adj last next) :
    chainLabelSpan realization (vertices ++ [next]) =
      chainLabelSpan realization vertices ⊔ (ℝ ∙ edgeLabel realization last next h) := by
  unfold chainLabelSpan
  rw [zip_tail_snoc vertices last next hlast, pairSpan_append, pairSpan_singleton]


private theorem zip_tail_overlap {α : Type*} (initial : List α) (middle : α) (final : List α) :
    (initial ++ middle :: final).zip (initial ++ middle :: final).tail =
      (initial ++ [middle]).zip (initial ++ [middle]).tail ++
        (middle :: final).zip final := by
  induction initial with
  | nil => rfl
  | cons first rest ih =>
    cases rest with
    | nil => rfl
    | cons second rest =>
      simp only [List.cons_append, List.tail_cons, List.zip_cons_cons]
      exact congrArg ((first, second) :: ·) ih

/-- Joining lists with a shared endpoint adds their chain-label spans. -/
theorem chainLabelSpan_overlap (initial : List W) (middle : W) (final : List W) :
    chainLabelSpan realization (initial ++ middle :: final) =
      chainLabelSpan realization (initial ++ [middle]) ⊔
        chainLabelSpan realization (middle :: final) := by
  unfold chainLabelSpan
  rw [zip_tail_overlap, pairSpan_append]
  rfl

end BruhatIntervals
