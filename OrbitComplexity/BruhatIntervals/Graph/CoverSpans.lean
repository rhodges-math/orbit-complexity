import OrbitComplexity.BruhatIntervals.Graph.Spans
import OrbitComplexity.BruhatIntervals.Graph.ThinIntervals

/-!
# Spanning interval labels by endpoint covers

The labels on the covers incident to either endpoint span all interval labels. The proof moves
an arbitrary cover through a rank-two diamond, by induction from the chosen endpoint.

## Main results

* `labelSpan_eq_covers`: all covers, bottom covers, and top covers give the same label span.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991), Section 3.
* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.7.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private noncomputable def bottomSpan (u v : W) : Submodule ℝ V :=
  Submodule.span ℝ
    {α : V | ∃ y ∈ bruhatInterval cs u v, ∃ h : (bruhatGraph cs).Adj u y,
      cs.length y = cs.length u + 1 ∧ edgeLabel realization u y h = α}

private noncomputable def topSpan (u v : W) : Submodule ℝ V :=
  Submodule.span ℝ
    {α : V | ∃ x ∈ bruhatInterval cs u v, ∃ h : (bruhatGraph cs).Adj x v,
      cs.length v = cs.length x + 1 ∧ edgeLabel realization x v h = α}

private theorem cover_mem_bottom (u v : W) :
    ∀ x ∈ bruhatInterval cs u v, ∀ y ∈ bruhatInterval cs u v,
      ∀ h : (bruhatGraph cs).Adj x y, cs.length y = cs.length x + 1 →
        edgeLabel realization x y h ∈ bottomSpan realization u v := by
  let : PartialOrder W := cs.bruhatPartialOrder
  suffices aux : ∀ n : ℕ, ∀ x y : W, cs.length x = n →
      x ∈ bruhatInterval cs u v → y ∈ bruhatInterval cs u v →
      ∀ h : (bruhatGraph cs).Adj x y, cs.length y = cs.length x + 1 →
        edgeLabel realization x y h ∈ bottomSpan realization u v by
    intro x hx y hy h hlength
    exact aux (cs.length x) x y rfl hx hy h hlength
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hlengthx hx hy hxy hlength
    by_cases hxu : x = u
    · subst x
      exact Submodule.subset_span ⟨y, hy, hxy, hlength, rfl⟩
    have hstep := bruhatStep_iff_adj.mpr ⟨hxy, by omega⟩
    have hcovxy : x ⋖ y := (bruhat_covBy_iff cs x y).mpr ⟨hstep.bruhatLE, hlength⟩
    obtain ⟨z, huz, hcovzx⟩ := exists_le_bruhat_covBy cs hx.1 (Ne.symm hxu)
    obtain ⟨x', ⟨hne, hcovzx', hcovx'y⟩, _⟩ :=
      bruhat_rank_two_diamond cs z x y hcovzx hcovxy
    have hzx := bruhat_covBy_step cs hcovzx
    have hzx' := bruhat_covBy_step cs hcovzx'
    have hx'y := bruhat_covBy_step cs hcovx'y
    have hzmem : z ∈ bruhatInterval cs u v := ⟨huz, hcovzx.le.trans hx.2⟩
    have hx'mem : x' ∈ bruhatInterval cs u v := ⟨huz.trans hcovzx'.le, hcovx'y.le.trans hy.2⟩
    have hzxlen := (bruhat_covBy_iff cs z x).mp hcovzx
    have hzx'len := (bruhat_covBy_iff cs z x').mp hcovzx'
    have hzyne : z ≠ y := by
      intro heq
      have hlt := hzx.length_lt.trans hstep.length_lt
      rw [heq] at hlt
      exact Nat.lt_irrefl _ hlt
    apply edgeLabel_mem_of_diamond realization
      (bruhatStep_iff_adj.mp hzx).1 (bruhatStep_iff_adj.mp hzx').1 hxy
      (bruhatStep_iff_adj.mp hx'y).1 (Ne.symm hne) hzyne (bottomSpan realization u v)
    · exact ih (cs.length z) (by omega) z x rfl hzmem hx _ hzxlen.2
    · exact ih (cs.length z) (by omega) z x' rfl hzmem hx'mem _ hzx'len.2

private theorem cover_mem_top (u v : W) :
    ∀ x ∈ bruhatInterval cs u v, ∀ y ∈ bruhatInterval cs u v,
      ∀ h : (bruhatGraph cs).Adj x y, cs.length y = cs.length x + 1 →
        edgeLabel realization x y h ∈ topSpan realization u v := by
  let : PartialOrder W := cs.bruhatPartialOrder
  suffices aux : ∀ n : ℕ, ∀ x y : W, cs.length v - cs.length y = n →
      x ∈ bruhatInterval cs u v → y ∈ bruhatInterval cs u v →
      ∀ h : (bruhatGraph cs).Adj x y, cs.length y = cs.length x + 1 →
        edgeLabel realization x y h ∈ topSpan realization u v by
    intro x hx y hy h hlength
    exact aux (cs.length v - cs.length y) x y rfl hx hy h hlength
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hgap hx hy hxy hlength
    by_cases hyv : y = v
    · subst y
      exact Submodule.subset_span ⟨x, hx, hxy, hlength, rfl⟩
    have hstep := bruhatStep_iff_adj.mpr ⟨hxy, by omega⟩
    have hcovxy : x ⋖ y := (bruhat_covBy_iff cs x y).mpr ⟨hstep.bruhatLE, hlength⟩
    obtain ⟨z, hcovyz, hzv⟩ := exists_bruhat_covBy_le cs hy.2 hyv
    obtain ⟨y', ⟨hne, hcovxy', hotherz⟩, _⟩ :=
      bruhat_rank_two_diamond cs x y z hcovxy hcovyz
    have hyz := bruhat_covBy_step cs hcovyz
    have hy'z := bruhat_covBy_step cs hotherz
    have hxy' := bruhat_covBy_step cs hcovxy'
    have hzmem : z ∈ bruhatInterval cs u v := ⟨hy.1.trans hcovyz.le, hzv⟩
    have hy'mem : y' ∈ bruhatInterval cs u v := ⟨hx.1.trans hcovxy'.le, hotherz.le.trans hzv⟩
    have hyzlen := (bruhat_covBy_iff cs y z).mp hcovyz
    have hy'zlen := (bruhat_covBy_iff cs y' z).mp hotherz
    have hzy : edgeLabel realization z y ((bruhatGraph cs).adj_symm
        (bruhatStep_iff_adj.mp hyz).1) ∈ topSpan realization u v := by
      rw [← edgeLabel_symm realization y z (bruhatStep_iff_adj.mp hyz).1]
      exact ih (cs.length v - cs.length z) (by
        have hzlength := hzv.length_le
        have hyzlength := hyz.length_lt
        omega) y z rfl hy hzmem _ hyzlen.2
    have hzy' : edgeLabel realization z y' ((bruhatGraph cs).adj_symm
        (bruhatStep_iff_adj.mp hy'z).1) ∈ topSpan realization u v := by
      rw [← edgeLabel_symm realization y' z (bruhatStep_iff_adj.mp hy'z).1]
      exact ih (cs.length v - cs.length z) (by
        have hzlength := hzv.length_le
        have hyzlength := hyz.length_lt
        omega) y' z rfl hy'mem hzmem _ hy'zlen.2
    rw [edgeLabel_symm realization x y hxy]
    apply edgeLabel_mem_of_diamond realization
      ((bruhatGraph cs).adj_symm (bruhatStep_iff_adj.mp hyz).1)
      ((bruhatGraph cs).adj_symm (bruhatStep_iff_adj.mp hy'z).1)
      ((bruhatGraph cs).adj_symm hxy)
      ((bruhatGraph cs).adj_symm (bruhatStep_iff_adj.mp hxy').1)
      (Ne.symm hne) ?_ (topSpan realization u v) hzy hzy'
    intro heq
    have hlt := hstep.length_lt.trans hyz.length_lt
    rw [heq] at hlt
    exact Nat.lt_irrefl _ hlt

/-- The covers of an interval, its bottom covers, and its top covers span all its edge labels. -/
theorem labelSpan_eq_covers (u v : W) (huv : cs.BruhatLE u v) :
    labelSpan realization u v = Submodule.span ℝ
      {α : V | ∃ x ∈ bruhatInterval cs u v, ∃ y ∈ bruhatInterval cs u v,
        ∃ h : (bruhatGraph cs).Adj x y, cs.length y = cs.length x + 1 ∧
          edgeLabel realization x y h = α} ∧
    labelSpan realization u v = Submodule.span ℝ
      {α : V | ∃ y ∈ bruhatInterval cs u v, ∃ h : (bruhatGraph cs).Adj u y,
        cs.length y = cs.length u + 1 ∧ edgeLabel realization u y h = α} ∧
    labelSpan realization u v = Submodule.span ℝ
      {α : V | ∃ x ∈ bruhatInterval cs u v, ∃ h : (bruhatGraph cs).Adj x v,
        cs.length v = cs.length x + 1 ∧ edgeLabel realization x v h = α} := by
  refine ⟨labelSpan_eq_all_covers realization u v, ?_, ?_⟩
  · change labelSpan realization u v = bottomSpan realization u v
    apply le_antisymm
    · rw [labelSpan_eq_all_covers]
      apply Submodule.span_le.mpr
      rintro α ⟨x, hx, y, hy, hxy, hlength, rfl⟩
      exact cover_mem_bottom realization u v x hx y hy hxy hlength
    · apply Submodule.span_le.mpr
      rintro α ⟨y, hy, hxy, hlength, rfl⟩
      exact Submodule.subset_span
        ⟨u, ⟨Relation.ReflTransGen.refl, huv⟩, y, hy, hxy, rfl⟩
  · change labelSpan realization u v = topSpan realization u v
    apply le_antisymm
    · rw [labelSpan_eq_all_covers]
      apply Submodule.span_le.mpr
      rintro α ⟨x, hx, y, hy, hxy, hlength, rfl⟩
      exact cover_mem_top realization u v x hx y hy hxy hlength
    · apply Submodule.span_le.mpr
      rintro α ⟨x, hx, hxy, hlength, rfl⟩
      exact Submodule.subset_span
        ⟨x, hx, v, ⟨huv, Relation.ReflTransGen.refl⟩, hxy, rfl⟩

end BruhatIntervals

