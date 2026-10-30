import OrbitComplexity.BruhatIntervals.Realizations.Reflections

/-!
# Comparing geometric realizations

The simple-root linear map from the free geometric space to any realization preserves pairings
with simple roots and intertwines the whole Coxeter action. Its injectivity is the independence
condition already carried by the realization.

## Main results

* `Realization.form_simple_linearCombination`: simple-root pairings agree in both spaces.
* `Realization.map_geometricReflection`: the simple-root map intertwines each simple reflection.
* `Realization.map_geometricAction`: the simple-root map intertwines the whole Coxeter action.

## Implementation notes

Additional ambient directions outside the span of the simple roots do not affect this comparison.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005), Chapter 4.
-/

namespace BruhatIntervals.Realization

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

/-- Pairing a simple root with a simple-root combination agrees with the free geometric form. -/
theorem form_simple_linearCombination (i : Index) (x : Index →₀ ℝ) :
    realization.form (realization.simpleRoot i)
        (Finsupp.linearCombination ℝ realization.simpleRoot x) =
      geometricForm matrix (geometricRoot i) x := by
  have hlinear : (realization.form (realization.simpleRoot i)).comp
      (Finsupp.linearCombination ℝ realization.simpleRoot) =
        geometricForm matrix (geometricRoot i) := by
    apply Finsupp.lhom_ext
    intro j c
    change realization.form (realization.simpleRoot i)
      (Finsupp.linearCombination ℝ realization.simpleRoot (Finsupp.single j c)) =
        geometricForm matrix (geometricRoot i) (Finsupp.single j c)
    rw [Finsupp.linearCombination_single, LinearMap.BilinForm.smul_right, realization.form_root]
    have hs : Finsupp.single j c = c • geometricRoot j := by
      simp only [geometricRoot, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, geometricForm_root]
    rfl
  exact LinearMap.congr_fun hlinear x

/-- The simple-root linear map intertwines a simple reflection. -/
theorem map_geometricReflection (i : Index) (x : Index →₀ ℝ) :
    Finsupp.linearCombination ℝ realization.simpleRoot (geometricReflection matrix i x) =
      realization.action (cs.simple i) (Finsupp.linearCombination ℝ realization.simpleRoot x) := by
  rw [geometricReflection_apply, map_sub, map_smul, geometricRoot,
    Finsupp.linearCombination_single, one_smul, realization.action_simple,
    realization.form_simple_linearCombination]
  rfl

/-- The simple-root linear map intertwines every Coxeter group element. -/
theorem map_geometricAction (w : W) (x : Index →₀ ℝ) :
    Finsupp.linearCombination ℝ realization.simpleRoot (geometricAction matrix cs w x) =
      realization.action w (Finsupp.linearCombination ℝ realization.simpleRoot x) := by
  suffices h : ∀ w : W, ∀ x : Index →₀ ℝ,
      Finsupp.linearCombination ℝ realization.simpleRoot (geometricAction matrix cs w x) =
        realization.action w (Finsupp.linearCombination ℝ realization.simpleRoot x) from h w x
  intro w
  apply cs.simple_induction_right w
  · intro x
    rw [map_one, map_one]
    rfl
  · intro v i ih x
    rw [map_mul, LinearEquiv.mul_apply, geometricAction_simple, ih,
      realization.map_geometricReflection, map_mul, LinearEquiv.mul_apply]

end BruhatIntervals.Realization
