import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.Canonical

/-!
# Roots of canonical reflections

Canonical reflections inherit positive roots from the ambient realization. Their distinct roots
have nonpositive pairings, and no three of them lie in one vector plane. The positive cone is
pointed; no nondegeneracy or positive definiteness of the geometric form is required.

## Main results

* `Realization.canonical_pairing_nonpos`: distinct canonical roots have nonpositive pairing.
* `Realization.canonical_root_not_mem_span`: a canonical root does not lie in the span of two
  other distinct canonical roots.

## Implementation notes

The canonical inversion property makes every canonical reflection preserve all other positive
subgroup roots. A putative positive pairing contradicts this property and the pointed cone.

## References

* M. Dyer, *Reflection Subgroups of Coxeter Systems*, Journal of Algebra 135 (1990), Section 4.
-/

namespace BruhatIntervals.Realization

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private theorem canonical_action_positive {H : Subgroup W} {t : W}
    (ht : t ∈ canonicalReflections cs H)
    (root : {x : V // x ∈ realization.positiveRoots})
    (hroot : (realization.rootReflection root).val ∈ H)
    (hne : (realization.rootReflection root).val ≠ t) :
    realization.action t root.val ∈ realization.positiveRoots := by
  have hnot : ¬cs.IsLeftInversion t (realization.rootReflection root).val := by
    intro hinv
    have hmem : (realization.rootReflection root).val ∈
        {r | cs.IsLeftInversion t r ∧ r ∈ H} := ⟨hinv, hroot⟩
    rw [ht.2, Set.mem_singleton_iff] at hmem
    exact hne hmem
  have hnegative : -realization.action t root.val ∉ realization.positiveRoots := by
    intro hneg
    apply hnot
    rw [realization.rootReflection_leftInversion_iff]
    exact ⟨root.property, by simpa only [ht.1.inv] using hneg⟩
  exact (realization.root_sign (realization.action_mem_roots t root.property.1)).resolve_right
    hnegative

/-- Distinct positive roots of canonical subgroup reflections have nonpositive pairing. -/
theorem canonical_pairing_nonpos {H : Subgroup W}
    (α β : {x : V // x ∈ realization.positiveRoots})
    (hα : (realization.rootReflection α).val ∈ canonicalReflections cs H)
    (hβ : (realization.rootReflection β).val ∈ canonicalReflections cs H) (hne : α ≠ β) :
    realization.form α.val β.val ≤ 0 := by
  by_contra hnot
  have hb : 0 < realization.form α.val β.val := lt_of_not_ge hnot
  have hαH := canonical_mem cs hα
  have hβH := canonical_mem cs hβ
  have href : (realization.rootReflection α).val ≠
      (realization.rootReflection β).val := by
    intro heq
    exact hne (realization.rootReflection_injective (Subtype.ext heq))
  have hγpos := canonical_action_positive realization hα β hβH href.symm
  let γ : {x : V // x ∈ realization.positiveRoots} :=
    ⟨realization.action (realization.rootReflection α).val β.val, hγpos⟩
  have hγH : (realization.rootReflection γ).val ∈ H := by
    rw [realization.rootReflection_conj (realization.rootReflection α).val β hγpos]
    exact H.mul_mem (H.mul_mem hαH hβH) (H.inv_mem hαH)
  have hγne : γ ≠ β := by
    intro heq
    have hval := congrArg Subtype.val heq
    change realization.action (realization.rootReflection α).val β.val = β.val at hval
    rw [realization.rootReflection_apply] at hval
    have hzero : (2 * realization.form α.val β.val) • α.val = 0 := sub_eq_self.mp hval
    exact (smul_ne_zero (by positivity) (realization.root_ne_zero α.property.1)) hzero
  have hγref : (realization.rootReflection γ).val ≠
      (realization.rootReflection β).val := by
    intro heq
    exact hγne (realization.rootReflection_injective (Subtype.ext heq))
  have hαpos := canonical_action_positive realization hβ α hαH href
  have hγpos' := canonical_action_positive realization hβ γ hγH hγref
  have hdecomp : β.val = (2 * realization.form α.val β.val) • α.val + γ.val := by
    dsimp only [γ]
    rw [realization.rootReflection_apply]
    abel
  have hself : realization.action (realization.rootReflection β).val β.val = -β.val := by
    rw [realization.rootReflection_apply, realization.form_root_eq_one β.property.1,
      mul_one, two_smul]
    abel
  have hnegative : -β.val ∈ realization.positiveCone := by
    rw [← hself, hdecomp, map_add, map_smul]
    exact realization.positiveCone_add
      (realization.positiveCone_smul (by positivity) hαpos.2) hγpos'.2
  exact realization.root_ne_zero β.property.1
    (realization.positiveCone_neg_eq_zero β.property.2 hnegative)

/-- A canonical positive root is outside the span of any two other distinct canonical roots. -/
theorem canonical_root_not_mem_span {H : Subgroup W}
    (α β γ : {x : V // x ∈ realization.positiveRoots})
    (hα : (realization.rootReflection α).val ∈ canonicalReflections cs H)
    (hβ : (realization.rootReflection β).val ∈ canonicalReflections cs H)
    (hγ : (realization.rootReflection γ).val ∈ canonicalReflections cs H)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) :
    γ.val ∉ Submodule.span ℝ ({α.val, β.val} : Set V) := by
  intro hspan
  obtain ⟨a, b, heq⟩ := Submodule.mem_span_pair.mp hspan
  have hAB := canonical_pairing_nonpos realization α β hα hβ hαβ
  have hAG := canonical_pairing_nonpos realization α γ hα hγ hαγ
  have hBG := canonical_pairing_nonpos realization β γ hβ hγ hβγ
  have hBA : realization.form β.val α.val ≤ 0 := by
    rwa [realization.form_isSymm.eq]
  have hGA : realization.form γ.val α.val ≤ 0 := by
    rwa [realization.form_isSymm.eq]
  have hGB : realization.form γ.val β.val ≤ 0 := by
    rwa [realization.form_isSymm.eq]
  have hA := congrArg (fun x => realization.form α.val x) heq
  have hB := congrArg (fun x => realization.form β.val x) heq
  have hG := congrArg (fun x => realization.form γ.val x) heq
  simp only [map_add, map_smul, smul_eq_mul,
    realization.form_root_eq_one α.property.1, mul_one] at hA
  simp only [map_add, map_smul, smul_eq_mul,
    realization.form_root_eq_one β.property.1, mul_one] at hB
  simp only [map_add, map_smul, smul_eq_mul,
    realization.form_root_eq_one γ.property.1] at hG
  by_cases ha : 0 < a
  · have hb : 0 < b := by
      by_contra hnot
      have := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hnot) hAB
      linarith
    have hfirst := mul_nonpos_of_nonneg_of_nonpos ha.le hGA
    have hsecond := mul_nonpos_of_nonneg_of_nonpos hb.le hGB
    linarith
  · have ha' : a ≤ 0 := le_of_not_gt ha
    have hb : b ≤ 0 := by
      have := mul_nonneg_of_nonpos_of_nonpos ha' hBA
      linarith
    have hnegative : -γ.val ∈ realization.positiveCone := by
      rw [← heq, neg_add_rev, ← neg_smul, ← neg_smul]
      exact realization.positiveCone_add
        (realization.positiveCone_smul (neg_nonneg.mpr hb) β.property.2)
        (realization.positiveCone_smul (neg_nonneg.mpr ha') α.property.2)
    exact realization.root_ne_zero γ.property.1
      (realization.positiveCone_neg_eq_zero γ.property.2 hnegative)

end BruhatIntervals.Realization
