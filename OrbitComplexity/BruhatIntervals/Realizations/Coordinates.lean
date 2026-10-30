import OrbitComplexity.BruhatIntervals.Realizations.Comparison

/-!
# Positive coordinates and geometric root labels

The canonical geometric cone consists of the vectors with nonnegative simple-root coordinates.
The simple-root comparison map therefore preserves positive roots and their reflection labels,
and maps the canonical label of every reflection to its label in any realization.

## Main results

* `geometricCone_iff`: the geometric cone is coordinatewise nonnegative.
* `Realization.map_geometric_positiveRoot`: the comparison map preserves positive roots.
* `Realization.map_geometric_rootReflection`: it preserves reflection labels.
* `Realization.map_geometric_label`: it transports a canonical label to the corresponding label.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005), Chapter 4.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W) [AddCommGroup V] [Module ℝ V]

private theorem geometric_linearCombination :
    Finsupp.linearCombination ℝ (geometricRoot : Index → Index →₀ ℝ) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i c
  rw [Finsupp.linearCombination_single]
  simp only [geometricRoot, Finsupp.smul_single, smul_eq_mul, mul_one, LinearMap.id_apply]

/-- The canonical geometric cone consists exactly of nonnegative coordinate vectors. -/
theorem geometricCone_iff (x : Index →₀ ℝ) :
    x ∈ (geometricRealization matrix cs).positiveCone ↔ ∀ i : Index, 0 ≤ x i := by
  constructor
  · rintro ⟨coefficients, hcoefficients, heq⟩
    change Finsupp.linearCombination ℝ geometricRoot coefficients = x at heq
    rw [geometric_linearCombination, LinearMap.id_apply] at heq
    exact heq ▸ hcoefficients
  · intro hx
    refine ⟨x, hx, ?_⟩
    change Finsupp.linearCombination ℝ geometricRoot x = x
    rw [geometric_linearCombination, LinearMap.id_apply]

namespace Realization

variable {cs} (realization : Realization cs (V := V))

/-- The simple-root comparison map sends geometric roots to roots of the realization. -/
theorem map_geometric_root {x : Index →₀ ℝ}
    (hx : x ∈ (geometricRealization matrix cs).roots) :
    Finsupp.linearCombination ℝ realization.simpleRoot x ∈ realization.roots := by
  obtain ⟨w, i, rfl⟩ := hx
  change Finsupp.linearCombination ℝ realization.simpleRoot
    (geometricAction matrix cs w (geometricRoot i)) ∈ realization.roots
  rw [realization.map_geometricAction]
  simp only [geometricRoot, Finsupp.linearCombination_single, one_smul]
  exact realization.action_mem_roots w (realization.simpleRoot_mem_roots i)

/-- The simple-root comparison map preserves positive roots. -/
theorem map_geometric_positiveRoot {x : Index →₀ ℝ}
    (hx : x ∈ (geometricRealization matrix cs).positiveRoots) :
    Finsupp.linearCombination ℝ realization.simpleRoot x ∈ realization.positiveRoots := by
  refine ⟨realization.map_geometric_root hx.1, x, ?_, rfl⟩
  exact (geometricCone_iff cs x).mp hx.2

/-- The simple-root comparison map preserves the Coxeter reflection of a positive root. -/
theorem map_geometric_rootReflection
    (root : {x : Index →₀ ℝ // x ∈ (geometricRealization matrix cs).positiveRoots}) :
    (realization.rootReflection
      ⟨Finsupp.linearCombination ℝ realization.simpleRoot root.val,
        realization.map_geometric_positiveRoot root.property⟩).val =
      ((geometricRealization matrix cs).rootReflection root).val := by
  obtain ⟨w, i, hroot⟩ := root.property.1
  have hmap : Finsupp.linearCombination ℝ realization.simpleRoot root.val =
      realization.action w (realization.simpleRoot i) := by
    rw [← hroot]
    change Finsupp.linearCombination ℝ realization.simpleRoot
      (geometricAction matrix cs w (geometricRoot i)) = _
    rw [realization.map_geometricAction]
    simp only [geometricRoot, Finsupp.linearCombination_single, one_smul]
  have hpos : realization.action w (realization.simpleRoot i) ∈ realization.positiveRoots := by
    rw [← hmap]
    exact realization.map_geometric_positiveRoot root.property
  have hsourcepos : (geometricRealization matrix cs).action w
      ((geometricRealization matrix cs).simpleRoot i) ∈
      (geometricRealization matrix cs).positiveRoots := hroot ▸ root.property
  have htarget :
      (⟨Finsupp.linearCombination ℝ realization.simpleRoot root.val,
        realization.map_geometric_positiveRoot root.property⟩ :
          {x : V // x ∈ realization.positiveRoots}) =
        ⟨realization.action w (realization.simpleRoot i), hpos⟩ := Subtype.ext hmap
  have hsource : root =
      ⟨(geometricRealization matrix cs).action w
        ((geometricRealization matrix cs).simpleRoot i), hsourcepos⟩ := Subtype.ext hroot.symm
  rw [htarget, realization.rootReflection_translated_simple, hsource,
    (geometricRealization matrix cs).rootReflection_translated_simple]

/-- The canonical geometric label of a reflection maps to its label in any realization. -/
theorem map_geometric_label (root : {x : V // x ∈ realization.positiveRoots}) :
    Finsupp.linearCombination ℝ realization.simpleRoot
      (((geometricRealization matrix cs).rootReflectionEquiv.symm
        (realization.rootReflection root)).val) = root.val := by
  let source := (geometricRealization matrix cs).rootReflectionEquiv.symm
    (realization.rootReflection root)
  have hsource : (geometricRealization matrix cs).rootReflection source =
      realization.rootReflection root :=
    (geometricRealization matrix cs).rootReflectionEquiv.apply_symm_apply
      (realization.rootReflection root)
  have htarget := realization.map_geometric_rootReflection source
  rw [congrArg Subtype.val hsource] at htarget
  have heq := realization.rootReflection_injective (Subtype.ext htarget)
  exact congrArg Subtype.val heq

end Realization
end BruhatIntervals
