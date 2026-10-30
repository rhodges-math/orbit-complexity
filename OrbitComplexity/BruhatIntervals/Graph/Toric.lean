import OrbitComplexity.BruhatIntervals.Graph.Dimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Toric intervals and maximal toric subintervals

Dimension changes across a rank-two diamond control the positions of zero increments along
saturated chains. Moving these increments yields maximal toric subintervals.

## Main results

* `swap_zero_one`: a one-dimensional increase across a diamond is attained at a middle vertex.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.2 and 2.7.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private theorem middle_eq_of_step (A B D : Submodule ℝ V)
    [FiniteDimensional ℝ B] [FiniteDimensional ℝ D]
    (hAB : A ≤ B) (hBD : B ≤ D)
    (hstep : Module.finrank ℝ D - Module.finrank ℝ A = 1) (hne : B ≠ D) : A = B := by
  have hlow := Submodule.finrank_mono hAB
  have hhigh := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hBD hne)
  exact Submodule.eq_of_le_of_finrank_eq hAB (by omega)


/-- If a two-cover diamond increases interval dimension by one, one middle interval already
has the upper interval's full label span. -/
theorem swap_zero_one (u v x y1 y2 : W) (huv : cs.BruhatLE u v)
    (hx : x ∈ bruhatInterval cs u v) (hy1 : y1 ∈ bruhatInterval cs u v)
    (hy2 : y2 ∈ bruhatInterval cs u v) (hne : y1 ≠ y2) :
    let : PartialOrder W := cs.bruhatPartialOrder
    x ⋖ y1 → y1 ⋖ v → x ⋖ y2 → y2 ⋖ v →
    algebraicDim realization u v - algebraicDim realization u x = 1 →
    labelSpan realization u v = labelSpan realization u y1 ∨
      labelSpan realization u v = labelSpan realization u y2 := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro hxy1 hy1v hxy2 hy2v hstep
  by_cases hfirst : labelSpan realization u v = labelSpan realization u y1
  · exact Or.inl hfirst
  by_cases hsecond : labelSpan realization u v = labelSpan realization u y2
  · exact Or.inr hsecond
  have hA1 := middle_eq_of_step (labelSpan realization u x)
    (labelSpan realization u y1) (labelSpan realization u v)
    (labelSpan_mono realization Relation.ReflTransGen.refl hxy1.le)
    (labelSpan_mono realization Relation.ReflTransGen.refl hy1v.le) hstep (Ne.symm hfirst)
  have hA2 := middle_eq_of_step (labelSpan realization u x)
    (labelSpan realization u y2) (labelSpan realization u v)
    (labelSpan_mono realization Relation.ReflTransGen.refl hxy2.le)
    (labelSpan_mono realization Relation.ReflTransGen.refl hy2v.le) hstep (Ne.symm hsecond)
  have ha := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hxy1)).1
  have hb := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hxy2)).1
  have hc := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hy1v)).1
  have hd := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hy2v)).1
  have hlabel1 : edgeLabel realization x y1 ha ∈ labelSpan realization u x := by
    rw [hA1]
    exact Submodule.subset_span
      ⟨x, ⟨hx.1, hxy1.le⟩, y1, ⟨hy1.1, Relation.ReflTransGen.refl⟩, ha, rfl⟩
  have hlabel2 : edgeLabel realization x y2 hb ∈ labelSpan realization u x := by
    rw [hA2]
    exact Submodule.subset_span
      ⟨x, ⟨hx.1, hxy2.le⟩, y2, ⟨hy2.1, Relation.ReflTransGen.refl⟩, hb, rfl⟩
  have hxvne : x ≠ v := by
    intro heq
    have hlt := (bruhat_covBy_step cs hxy1).length_lt.trans
      (bruhat_covBy_step cs hy1v).length_lt
    rw [heq] at hlt
    exact Nat.lt_irrefl _ hlt
  have hupper := edgeLabel_mem_of_diamond realization ha hb hc hd hne hxvne
    (labelSpan realization u x) hlabel1 hlabel2
  have hlength := ((bruhat_covBy_iff cs y1 v).mp hy1v).2
  have hformula := (labelSpan_properties realization u v huv).1 y1 hy1 hc hlength
  apply False.elim
  apply hfirst
  apply hformula.trans
  apply sup_eq_left.mpr
  apply Submodule.span_le.mpr
  rintro root rfl
  exact hA1 ▸ hupper

end BruhatIntervals

