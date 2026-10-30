import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.Roots
import OrbitComplexity.BruhatIntervals.Realizations.Independence
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Canonical reflections in a plane

A subgroup whose canonical roots lie in a vector plane has at most two canonical reflections.
The proof uses the dimension of a distinct positive-root pair and the fact that a third canonical
root lies outside their span. The identity fills an empty slot when the canonical set is empty.

## Main results

* `Realization.canonical_subset_pair`: canonical reflections in a plane are contained in a pair.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991),
  Section 3.
-/

namespace BruhatIntervals.Realization

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

/-- At most two canonical reflections have their positive roots in one vector plane. -/
theorem canonical_subset_pair (H : Subgroup W) (plane : Submodule ℝ V)
    [FiniteDimensional ℝ plane] (hdim : Module.finrank ℝ plane ≤ 2)
    (hplane : ∀ root : {x : V // x ∈ realization.positiveRoots},
      (realization.rootReflection root).val ∈ canonicalReflections cs H → root.val ∈ plane) :
    ∃ r s : W, r ∈ insert 1 (canonicalReflections cs H) ∧
      s ∈ insert 1 (canonicalReflections cs H) ∧ canonicalReflections cs H ⊆ {r, s} := by
  classical
  by_cases hnonempty : (canonicalReflections cs H).Nonempty
  · obtain ⟨r, hr⟩ := hnonempty
    by_cases hsingle : ∀ s ∈ canonicalReflections cs H, s = r
    · refine ⟨r, r, Or.inr hr, Or.inr hr, ?_⟩
      intro t ht
      change t = r ∨ t = r
      exact Or.inl (hsingle t ht)
    · push Not at hsingle
      obtain ⟨s, hs, hsr⟩ := hsingle
      obtain ⟨α, hα⟩ := realization.rootReflection_surjective ⟨r, hr.1⟩
      obtain ⟨β, hβ⟩ := realization.rootReflection_surjective ⟨s, hs.1⟩
      have hαval := congrArg Subtype.val hα
      have hβval := congrArg Subtype.val hβ
      have hαcan : (realization.rootReflection α).val ∈ canonicalReflections cs H := by
        simpa only [hαval] using hr
      have hβcan : (realization.rootReflection β).val ∈ canonicalReflections cs H := by
        simpa only [hβval] using hs
      have hαβ : α ≠ β := by
        intro heq
        apply hsr
        exact ((hαval.symm.trans
          (congrArg (fun root => (realization.rootReflection root).val) heq)).trans hβval).symm
      have hle : Submodule.span ℝ ({α.val, β.val} : Set V) ≤ plane :=
        Submodule.span_le.mpr (Set.pair_subset (hplane α hαcan) (hplane β hβcan))
      have hspaneq : Submodule.span ℝ ({α.val, β.val} : Set V) = plane := by
        apply Submodule.eq_of_le_of_finrank_le hle
        rw [realization.positiveRoots_pair_finrank α β hαβ]
        exact hdim
      refine ⟨r, s, Or.inr hr, Or.inr hs, ?_⟩
      intro t ht
      change t = r ∨ t = s
      by_cases htr : t = r
      · exact Or.inl htr
      by_cases hts : t = s
      · exact Or.inr hts
      exfalso
      obtain ⟨γ, hγ⟩ := realization.rootReflection_surjective ⟨t, ht.1⟩
      have hγval := congrArg Subtype.val hγ
      have hγcan : (realization.rootReflection γ).val ∈ canonicalReflections cs H := by
        simpa only [hγval] using ht
      have hαγ : α ≠ γ := by
        intro heq
        apply htr
        exact ((hαval.symm.trans
          (congrArg (fun root => (realization.rootReflection root).val) heq)).trans hγval).symm
      have hβγ : β ≠ γ := by
        intro heq
        apply hts
        exact ((hβval.symm.trans
          (congrArg (fun root => (realization.rootReflection root).val) heq)).trans hγval).symm
      apply realization.canonical_root_not_mem_span α β γ hαcan hβcan hγcan hαβ hαγ hβγ
      rw [hspaneq]
      exact hplane γ hγcan
  · refine ⟨1, 1, Or.inl rfl, Or.inl rfl, ?_⟩
    intro t ht
    exact (hnonempty ⟨t, ht⟩).elim

end BruhatIntervals.Realization
