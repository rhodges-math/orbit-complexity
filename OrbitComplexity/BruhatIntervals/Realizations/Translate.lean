import OrbitComplexity.BruhatIntervals.Realizations.Conjugation

/-!
# Positive roots under translation

The positive representative of a translated root labels the conjugated reflection. It is either
the translated root or its negative, according to its sign in the ambient realization.

## Main results

* `Realization.rootReflection_simple`: a simple root has its simple Coxeter reflection.
* `Realization.exists_positive_translate`: every translated root has a positive representative
  with the conjugated reflection.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005), Section 4.4.
-/

namespace BruhatIntervals.Realization

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

/-- The reflection of a positive simple root is its simple Coxeter generator. -/
theorem rootReflection_simple (i : Index) :
    (realization.rootReflection
      ⟨realization.simpleRoot i, realization.simpleRoot_mem_positiveRoots i⟩).val =
      cs.simple i := by
  apply realization.action_injective
  apply LinearEquiv.ext
  intro x
  rw [realization.rootReflection_apply, realization.action_simple]

/-- A translated root has a positive sign representative labeling the conjugated reflection. -/
theorem exists_positive_translate (w : W)
    (root : {x : V // x ∈ realization.positiveRoots}) :
    ∃ image : {x : V // x ∈ realization.positiveRoots},
      (image.val = realization.action w root.val ∨
        image.val = -realization.action w root.val) ∧
      (realization.rootReflection image).val =
        w * (realization.rootReflection root).val * w⁻¹ := by
  rcases realization.root_sign (realization.action_mem_roots w root.property.1) with hpos | hneg
  · exact ⟨⟨realization.action w root.val, hpos⟩, Or.inl rfl,
      realization.rootReflection_conj w root hpos⟩
  · exact ⟨⟨-realization.action w root.val, hneg⟩, Or.inr rfl,
      realization.rootReflection_conj_neg w root hneg⟩

end BruhatIntervals.Realization
