import OrbitComplexity.BruhatIntervals.Graph.CoverSpans

/-! # Inversion roots and lower interval spans

The top-cover labels of a lower interval are inversion roots. Conversely, every inversion
reflection gives a downward edge at the upper endpoint, so these roots span all interval labels.
-/

namespace BruhatIntervals

universe u v z
variable {S : Type u} {W : Type v} {V : Type z} [Group W] {M : CoxeterMatrix S}
  {cs : CoxeterSystem M W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

/-- The labels of a lower interval span exactly its upper element's inversion roots. -/
theorem labelSpan_one_inversions (w : W) :
    labelSpan realization 1 w = Submodule.span ℝ (realization.inversionRoots w) := by
  apply le_antisymm
  · rw [(labelSpan_eq_covers realization 1 w (cs.one_bruhatLE w)).2.2]
    apply Submodule.span_le.mpr
    rintro α ⟨x, hx, hxw, hlength, rfl⟩
    let root : {α : V // α ∈ realization.positiveRoots} :=
      ⟨edgeLabel realization x w hxw, edgeLabel_positive realization x w hxw⟩
    have htarget : w = (realization.rootReflection root).val * x :=
      edgeLabel_target realization x w hxw
    have htw : (realization.rootReflection root).val * w = x := by
      rw [htarget, ← mul_assoc, (realization.rootReflection root).property.mul_self, one_mul]
    apply Submodule.subset_span
    exact (realization.rootReflection_length_iff w root).mp (by rw [htw]; omega)
  · apply Submodule.span_le.mpr
    intro α hα
    let root : {α : V // α ∈ realization.positiveRoots} := ⟨α, hα.1⟩
    let x := (realization.rootReflection root).val * w
    have hlt : cs.length x < cs.length w :=
      (realization.rootReflection_length_iff w root).mpr hα
    have htarget : w = (realization.rootReflection root).val * x := by
      dsimp only [x]
      rw [← mul_assoc, (realization.rootReflection root).property.mul_self, one_mul]
    have hadj : (bruhatGraph cs).Adj x w :=
      (bruhatGraph_adj_iff realization x w).mpr ⟨root, htarget⟩
    have hstep : cs.BruhatStep x w := bruhatStep_iff_adj.mpr ⟨hadj, hlt⟩
    change α ∈ Submodule.span ℝ {β : V | ∃ y ∈ bruhatInterval cs 1 w,
      ∃ z ∈ bruhatInterval cs 1 w, ∃ h : (bruhatGraph cs).Adj y z,
        edgeLabel realization y z h = β}
    exact Submodule.subset_span ⟨x, ⟨cs.one_bruhatLE x, hstep.bruhatLE⟩,
      w, ⟨cs.one_bruhatLE w, cs.bruhatLE_refl w⟩, hadj,
      edgeLabel_unique realization hadj root htarget⟩

end BruhatIntervals
