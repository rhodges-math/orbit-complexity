import OrbitComplexity.BruhatIntervals.Realizations.Range
import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.Dihedral

/-!
# Reflection products with independent pairing functionals

Two equal nonidentity products of root reflections span the same root plane whenever the first
pair's pairing functionals are independent. Their four reflections generate a dihedral subgroup,
constructed from its canonical reflections in that plane.

## Main results

* `Realization.rootProduct_plane`: equal products with a nonsingular pairing matrix determine
  one two-dimensional root plane and a dihedral reflection subgroup.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991), Section 3.
-/

namespace BruhatIntervals.Realization

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private theorem range_le_rootSpan (α β : {x : V // x ∈ realization.positiveRoots}) :
    LinearMap.range (LinearMap.id -
      (realization.action ((realization.rootReflection α).val *
        (realization.rootReflection β).val)).toLinearMap) ≤
      Submodule.span ℝ ({α.val, β.val} : Set V) := by
  rintro z ⟨w, rfl⟩
  change w - realization.action
    ((realization.rootReflection α).val * (realization.rootReflection β).val) w ∈ _
  rw [map_mul, LinearEquiv.mul_apply, realization.rootReflection_apply,
    realization.rootReflection_apply]
  let plane := Submodule.span ℝ ({α.val, β.val} : Set V)
  have hα : α.val ∈ plane := Submodule.subset_span (Or.inl rfl)
  have hβ : β.val ∈ plane := Submodule.subset_span (Or.inr rfl)
  convert plane.add_mem
    (plane.smul_mem (2 * realization.form β.val w) hβ)
    (plane.smul_mem
      (2 * realization.form α.val (w - (2 * realization.form β.val w) • β.val)) hα) using 1
  abel

/-- Equal nonidentity root products with independent pairing functionals have the same
two-dimensional span, and their reflections generate a dihedral subgroup. -/
theorem rootProduct_plane
    (α β γ τ : {x : V // x ∈ realization.positiveRoots})
    (hprod : (realization.rootReflection α).val * (realization.rootReflection β).val =
      (realization.rootReflection γ).val * (realization.rootReflection τ).val)
    (hne : (realization.rootReflection α).val * (realization.rootReflection β).val ≠ 1)
    (x y : V) (hdet : realization.form α.val x * realization.form β.val y -
      realization.form α.val y * realization.form β.val x ≠ 0) :
    Submodule.span ℝ ({α.val, β.val} : Set V) =
      Submodule.span ℝ ({γ.val, τ.val} : Set V) ∧
    Module.finrank ℝ (Submodule.span ℝ ({α.val, β.val} : Set V)) = 2 ∧
    ∃ n : ℕ, Nonempty (DihedralGroup n ≃* Subgroup.closure
      ((fun root => (realization.rootReflection root).val) ''
        ({α, β, γ, τ} : Set {x : V // x ∈ realization.positiveRoots}))) := by
  have hαβ : α ≠ β := by
    intro heq
    apply hne
    rw [heq]
    exact (realization.rootReflection β).property.mul_self
  have hγτ : γ ≠ τ := by
    intro heq
    apply hne
    rw [hprod, heq]
    exact (realization.rootReflection τ).property.mul_self
  have hfirst := realization.positiveRoots_pair_finrank α β hαβ
  have hsecond := realization.positiveRoots_pair_finrank γ τ hγτ
  have : FiniteDimensional ℝ (Submodule.span ℝ ({γ.val, τ.val} : Set V)) :=
    FiniteDimensional.span_of_finite ℝ (Set.toFinite _)
  have hle : Submodule.span ℝ ({α.val, β.val} : Set V) ≤
      Submodule.span ℝ ({γ.val, τ.val} : Set V) := by
    rw [← realization.rootProduct_range α β x y hdet, hprod]
    exact range_le_rootSpan realization γ τ
  have heq := Submodule.eq_of_le_of_finrank_eq hle (hfirst.trans hsecond.symm)
  refine ⟨heq, hfirst, ?_⟩
  have : FiniteDimensional ℝ (Submodule.span ℝ ({α.val, β.val} : Set V)) :=
    FiniteDimensional.span_of_finite ℝ (Set.toFinite _)
  apply realization.reflection_closure_dihedral
    (Submodule.span ℝ ({α.val, β.val} : Set V)) hfirst.le
  · intro root hroot
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hroot
    rcases hroot with rfl | rfl | rfl | rfl
    · exact Submodule.subset_span (Or.inl rfl)
    · exact Submodule.subset_span (Or.inr rfl)
    · rw [heq]
      exact Submodule.subset_span (Or.inl rfl)
    · rw [heq]
      exact Submodule.subset_span (Or.inr rfl)
  · exact ⟨α, Or.inl rfl, β, Or.inr (Or.inl rfl), hαβ⟩

end BruhatIntervals.Realization
