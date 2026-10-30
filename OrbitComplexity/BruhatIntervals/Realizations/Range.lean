import OrbitComplexity.BruhatIntervals.Realizations.Reflections
import Mathlib.Tactic.Module

/-!
# Displacement spaces of two root reflections

The displacement space of a product of two root reflections equals their root plane whenever
the two root-pairing functionals are independent. Two explicit test vectors certify that
independence; the geometric form itself may be degenerate.

## Main results

* `Realization.rootProduct_range`: a nonsingular pairing matrix identifies the displacement space
  of a two-reflection product with the span of its roots.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991), Section 3.
-/

namespace BruhatIntervals.Realization

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private theorem span_pair_le {x y : V} {A B C D : ℝ} (plane : Submodule ℝ V)
    (hdet : A * D - B * C ≠ 0) (hfirst : A • x + B • y ∈ plane)
    (hsecond : C • x + D • y ∈ plane) :
    Submodule.span ℝ ({x, y} : Set V) ≤ plane := by
  apply Submodule.span_le.mpr
  apply Set.pair_subset
  · change x ∈ plane
    have h := plane.sub_mem (plane.smul_mem D hfirst) (plane.smul_mem B hsecond)
    have heq : D • (A • x + B • y) - B • (C • x + D • y) =
        (A * D - B * C) • x := by module
    rw [heq] at h
    simpa only [smul_smul, inv_mul_cancel₀ hdet, one_smul] using
      plane.smul_mem (A * D - B * C)⁻¹ h
  · change y ∈ plane
    have h := plane.sub_mem (plane.smul_mem A hsecond) (plane.smul_mem C hfirst)
    have heq : A • (C • x + D • y) - C • (A • x + B • y) =
        (A * D - B * C) • y := by module
    rw [heq] at h
    simpa only [smul_smul, inv_mul_cancel₀ hdet, one_smul] using
      plane.smul_mem (A * D - B * C)⁻¹ h

/-- Two independent root-pairing functionals identify the displacement range of the root product
with the span of its two roots. -/
theorem rootProduct_range (α β : {x : V // x ∈ realization.positiveRoots}) (x y : V)
    (hdet : realization.form α.val x * realization.form β.val y -
      realization.form α.val y * realization.form β.val x ≠ 0) :
    LinearMap.range (LinearMap.id -
      (realization.action ((realization.rootReflection α).val *
        (realization.rootReflection β).val)).toLinearMap) =
      Submodule.span ℝ ({α.val, β.val} : Set V) := by
  let displacement : V →ₗ[ℝ] V := LinearMap.id -
    (realization.action ((realization.rootReflection α).val *
      (realization.rootReflection β).val)).toLinearMap
  have hformula (z : V) : displacement z =
      (2 * realization.form α.val z -
        4 * realization.form α.val β.val * realization.form β.val z) • α.val +
        (2 * realization.form β.val z) • β.val := by
    dsimp only [displacement, LinearMap.sub_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe]
    rw [map_mul, LinearEquiv.mul_apply, realization.rootReflection_apply,
      realization.rootReflection_apply, map_sub, map_smul]
    module
  have hdet' :
      (2 * realization.form α.val x -
        4 * realization.form α.val β.val * realization.form β.val x) *
          (2 * realization.form β.val y) -
      (2 * realization.form β.val x) *
        (2 * realization.form α.val y -
          4 * realization.form α.val β.val * realization.form β.val y) ≠ 0 := by
    have heq :
        (2 * realization.form α.val x -
          4 * realization.form α.val β.val * realization.form β.val x) *
            (2 * realization.form β.val y) -
        (2 * realization.form β.val x) *
          (2 * realization.form α.val y -
            4 * realization.form α.val β.val * realization.form β.val y) =
          4 * (realization.form α.val x * realization.form β.val y -
            realization.form α.val y * realization.form β.val x) := by ring
    rw [heq]
    exact mul_ne_zero (by norm_num) hdet
  change LinearMap.range displacement = _
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    rw [hformula]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl rfl))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))
  · apply span_pair_le (LinearMap.range displacement) hdet'
    · rw [← hformula x]
      exact ⟨x, rfl⟩
    · rw [← hformula y]
      exact ⟨y, rfl⟩

end BruhatIntervals.Realization
