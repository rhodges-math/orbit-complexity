import OrbitComplexity.BruhatIntervals.Graph.Basic
import OrbitComplexity.BruhatIntervals.Graph.IntervalPaths
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.Dimension
import Batteries.Tactic.Lint

/-! # Convex hulls of Bruhat interval weights

The differences of weights in a Bruhat interval span its edge labels when no
root pairing vanishes on the weight orbit. Consequently the affine dimension
of the interval convex hull is its algebraic dimension.

## References

* E. Tsukerman and L. Williams, *Bruhat interval polytopes*, Adv. Math. 285 (2015), 766–810,
  Definition 7.8.
-/

namespace BruhatIntervals

noncomputable section

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

/-- The interval polytope is the convex hull of the weights of its Coxeter group elements. -/
def intervalPolytope (u v : W) (weight : V) : Set V :=
  convexHull ℝ ((fun w => realization.action w weight) '' bruhatInterval cs u v)

/-- Scaling the weight scales the interval polytope by the same real scalar. -/
theorem intervalPolytope_smul (u v : W) (a : ℝ) (weight : V) :
    intervalPolytope realization u v (a • weight) =
      (fun q => a • q) '' intervalPolytope realization u v weight := by
  have hscale : (LinearMap.lsmul ℝ V a : V → V) = (fun q => a • q) := by
    funext q
    exact LinearMap.lsmul_apply a q
  simpa only [intervalPolytope, Set.image_image, Function.comp_def,
    LinearEquiv.map_smul, LinearMap.lsmul_apply, hscale] using
    ((LinearMap.lsmul ℝ V a).image_convexHull
      ((fun w => realization.action w weight) '' bruhatInterval cs u v)).symm

/-- A nonempty Bruhat interval gives a nonempty interval polytope. -/
theorem intervalPolytope_nonempty (u v : W) (huv : cs.BruhatLE u v) (weight : V) :
    (intervalPolytope realization u v weight).Nonempty := by
  refine ⟨realization.action u weight, ?_⟩
  exact subset_convexHull ℝ _ (Set.mem_image_of_mem _ ⟨cs.bruhatLE_refl u, huv⟩)

private theorem edge_displacement (x y : W) (hxy : (bruhatGraph cs).Adj x y) (weight : V) :
    realization.action y weight - realization.action x weight =
      -(2 * realization.form (edgeLabel realization x y hxy)
        (realization.action x weight)) • edgeLabel realization x y hxy := by
  have hy := congrArg (fun w => realization.action w weight)
    (edgeLabel_target realization x y hxy)
  simp only [map_mul, LinearEquiv.mul_apply, Realization.rootReflection_apply] at hy
  rw [hy]
  module

private theorem displacement_mem (u v : W) (huv : cs.BruhatLE u v) (weight : V)
    (x : bruhatInterval cs u v) :
    realization.action x.val weight - realization.action u weight ∈ labelSpan realization u v := by
  let : PartialOrder W := cs.bruhatPartialOrder
  have hpath := bruhatInterval_cover_reachable cs u v huv x
  induction hpath with
  | refl => simp
  | @tail y z hpath hstep ih =>
    have hadj : (bruhatGraph cs).Adj y.val z.val :=
      ((bruhatStep_iff_adj (cs := cs)).mp (bruhat_covBy_step cs hstep)).1
    have hlabel : edgeLabel realization y.val z.val hadj ∈ labelSpan realization u v :=
      Submodule.subset_span ⟨y.val, y.property, z.val, z.property, hadj, rfl⟩
    have hdiff : realization.action z.val weight - realization.action y.val weight ∈
        labelSpan realization u v := by
      rw [edge_displacement realization y.val z.val hadj weight]
      exact Submodule.smul_mem _ _ hlabel
    have heq : realization.action z.val weight - realization.action u weight =
        (realization.action z.val weight - realization.action y.val weight) +
          (realization.action y.val weight - realization.action u weight) := by abel
    rw [heq]
    exact Submodule.add_mem _ hdiff ih

/-- At a weight with nonzero root pairings, interval differences span the edge labels. -/
theorem labelSpan_eq_span_sub (u v : W) (huv : cs.BruhatLE u v) (weight : V)
    (hregular : ∀ (w : W) (α : {x : V // x ∈ realization.positiveRoots}),
      realization.form α.val (realization.action w weight) ≠ 0) :
    labelSpan realization u v = Submodule.span ℝ
      ((fun w => realization.action w weight - realization.action u weight) ''
        bruhatInterval cs u v) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, y, hy, hxy, rfl⟩
    have hxmem := Submodule.subset_span (R := ℝ)
      (Set.mem_image_of_mem (fun w => realization.action w weight - realization.action u weight) hx)
    have hymem := Submodule.subset_span (R := ℝ)
      (Set.mem_image_of_mem (fun w => realization.action w weight - realization.action u weight) hy)
    have hdiff := Submodule.sub_mem _ hymem hxmem
    have heq : (realization.action y weight - realization.action u weight) -
        (realization.action x weight - realization.action u weight) =
          realization.action y weight - realization.action x weight := by abel
    rw [heq, edge_displacement realization x y hxy weight] at hdiff
    exact (Submodule.smul_mem_iff _
      (neg_ne_zero.mpr (mul_ne_zero (by norm_num)
        (hregular x ⟨edgeLabel realization x y hxy,
          edgeLabel_positive realization x y hxy⟩)))).mp hdiff
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    exact displacement_mem realization u v huv weight ⟨x, hx⟩

/-- The direction of the interval polytope is its interval label span. -/
theorem intervalPolytope_direction (u v : W) (huv : cs.BruhatLE u v) (weight : V)
    (hregular : ∀ (w : W) (α : {x : V // x ∈ realization.positiveRoots}),
      realization.form α.val (realization.action w weight) ≠ 0) :
    (affineSpan ℝ (intervalPolytope realization u v weight)).direction =
      labelSpan realization u v := by
  have hu : realization.action u weight ∈
      ((fun w => realization.action w weight) '' bruhatInterval cs u v) :=
    Set.mem_image_of_mem _ ⟨cs.bruhatLE_refl u, huv⟩
  rw [intervalPolytope, affineSpan_convexHull, direction_affineSpan,
    vectorSpan_eq_span_vsub_set_right ℝ hu]
  simpa only [Set.image_image, vsub_eq_sub, Function.comp_apply] using
    (labelSpan_eq_span_sub realization u v huv weight hregular).symm

/-- Differences of all points of a regular interval polytope span its edge labels. -/
theorem intervalPolytope_span_sub (u v : W) (huv : cs.BruhatLE u v) (weight : V)
    (hregular : ∀ (w : W) (α : {x : V // x ∈ realization.positiveRoots}),
      realization.form α.val (realization.action w weight) ≠ 0) :
    Submodule.span ℝ ((fun q => q - realization.action u weight) ''
      intervalPolytope realization u v weight) = labelSpan realization u v := by
  have hu : realization.action u weight ∈ intervalPolytope realization u v weight :=
    subset_convexHull ℝ _ (Set.mem_image_of_mem _ ⟨cs.bruhatLE_refl u, huv⟩)
  calc
    _ = vectorSpan ℝ (intervalPolytope realization u v weight) := by
      simpa only [vsub_eq_sub] using (vectorSpan_eq_span_vsub_set_right ℝ hu).symm
    _ = labelSpan realization u v := by
      rw [← direction_affineSpan, intervalPolytope_direction realization u v huv weight hregular]

/-- The direction of a regular interval polytope has the algebraic dimension. -/
theorem intervalPolytope_finrank (u v : W) (huv : cs.BruhatLE u v) (weight : V)
    (hregular : ∀ (w : W) (α : {x : V // x ∈ realization.positiveRoots}),
      realization.form α.val (realization.action w weight) ≠ 0) :
    Module.finrank ℝ (affineSpan ℝ (intervalPolytope realization u v weight)).direction =
      algebraicDim realization u v := by
  rw [intervalPolytope_direction realization u v huv weight hregular]
  rfl

/-- The affine dimension of a regular interval polytope is its algebraic dimension. -/
theorem intervalPolytope_finDim (u v : W) (huv : cs.BruhatLE u v) (weight : V)
    (hregular : ∀ (w : W) (α : {x : V // x ∈ realization.positiveRoots}),
      realization.form α.val (realization.action w weight) ≠ 0) :
    (affineSpan ℝ (intervalPolytope realization u v weight)).finDim =
      (algebraicDim realization u v : WithBot ℕ) := by
  rw [AffineSubspace.finDim_eq_finrank
    ((bot_lt_affineSpan ℝ).mpr (intervalPolytope_nonempty realization u v huv weight)).ne']
  exact_mod_cast intervalPolytope_finrank realization u v huv weight hregular

/-- Definition 7.8 of Tsukerman–Williams: the Bruhat interval polytope of `[u, v]` for a weight is
the convex hull of the images of the weight under the elements of the interval. It is nonempty
when `u ≤ v`, and scaling the weight scales the polytope. -/
theorem intervalPolytope_definition (u v : W) (weight : V) :
    intervalPolytope realization u v weight =
      convexHull ℝ ((fun w => realization.action w weight) '' bruhatInterval cs u v) ∧
    (cs.BruhatLE u v → (intervalPolytope realization u v weight).Nonempty) ∧
    ∀ a : ℝ, intervalPolytope realization u v (a • weight) =
      (fun q => a • q) '' intervalPolytope realization u v weight :=
  ⟨rfl, fun huv => intervalPolytope_nonempty realization u v huv weight,
    fun a => intervalPolytope_smul realization u v a weight⟩

end

end BruhatIntervals
