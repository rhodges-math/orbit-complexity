import OrbitComplexity.BruhatIntervals.Realizations.Inversions

/-!
# Positive roots and reflections

Positive roots are in bijection with Coxeter reflections. Their geometric reflection formula
identifies the two inversion notions: left multiplication by a root reflection decreases length
exactly when that root belongs to the left inversion set.

## Main definitions

* `Realization.rootReflection`: the Coxeter reflection associated with a positive root.
* `Realization.rootReflectionEquiv`: the equivalence between positive roots and reflections.

## Main results

* `Realization.rootReflection_apply`: the action of a root reflection is its geometric reflection.
* `Realization.rootReflection_length_iff`: left length decrease is inversion-root membership.
* `Realization.rootReflection_right_length`: right length decrease is negativity of the root image.

## Implementation notes

Faithfulness identifies the conjugates of the simple actions. Independence and unit root length
make the associated positive root unique, even when the ambient geometric form is degenerate.
The length criterion is proved using reduced inversion sequences.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 4.4.
-/

namespace BruhatIntervals.Realization

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

/-- A conjugated simple generator acts by reflection in the translated simple root. -/
theorem action_conjugate_simple (w : W) (i : Index) (y : V) :
    realization.action (w * cs.simple i * w⁻¹) y =
      y - (2 * realization.form (realization.action w (realization.simpleRoot i)) y) •
        realization.action w (realization.simpleRoot i) := by
  have hpair : realization.form (realization.simpleRoot i) (realization.action (w⁻¹) y) =
      realization.form (realization.action w (realization.simpleRoot i)) y := by
    have h := realization.action_form w (realization.simpleRoot i) (realization.action (w⁻¹) y)
    rw [realization.action_action_inv] at h
    exact h.symm
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    realization.action_simple, map_sub, map_smul, realization.action_action_inv, hpair]

private theorem exists_reflection_action {x : V} (hx : x ∈ realization.roots) :
    ∃ t : W, cs.IsReflection t ∧
      ∀ y : V, realization.action t y = y - (2 * realization.form x y) • x := by
  obtain ⟨w, i, rfl⟩ := hx
  refine ⟨w * cs.simple i * w⁻¹, (cs.isReflection_simple i).conj w, ?_⟩
  exact realization.action_conjugate_simple w i

/-- The Coxeter reflection associated with a positive root. -/
noncomputable def rootReflection (root : {x : V // x ∈ realization.positiveRoots}) :
    {t : W // cs.IsReflection t} :=
  ⟨Classical.choose (exists_reflection_action realization root.property.1),
    (Classical.choose_spec (exists_reflection_action realization root.property.1)).1⟩

/-- The Coxeter reflection of a positive root acts by its reflection formula. -/
theorem rootReflection_apply (root : {x : V // x ∈ realization.positiveRoots}) (y : V) :
    realization.action (realization.rootReflection root).val y =
      y - (2 * realization.form root.val y) • root.val :=
  (Classical.choose_spec (exists_reflection_action realization root.property.1)).2 y

/-- Different positive roots give different Coxeter reflections. -/
theorem rootReflection_injective : Function.Injective realization.rootReflection := by
  intro α β heq
  have h := congrArg (fun t : {t : W // cs.IsReflection t} =>
    realization.action t.val α.val) heq
  rw [realization.rootReflection_apply, realization.rootReflection_apply,
    realization.form_root_eq_one α.property.1, mul_one] at h
  have htwice : (2 : ℝ) • α.val =
      (2 * realization.form β.val α.val) • β.val := by
    simpa only [sub_sub_cancel] using congrArg (fun z : V => α.val - z) h
  have hcol : α.val = (realization.form β.val α.val) • β.val := by
    apply smul_right_injective V (by norm_num : (2 : ℝ) ≠ 0)
    change (2 : ℝ) • α.val = (2 : ℝ) • ((realization.form β.val α.val) • β.val)
    rw [smul_smul]
    exact htwice
  have hunit := realization.form_root_eq_one α.property.1
  rw [hcol, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    realization.form_root_eq_one β.property.1, mul_one] at hunit
  rcases mul_self_eq_one_iff.mp hunit with hpositive | hnegative
  · apply Subtype.ext
    simpa only [hpositive, one_smul] using hcol
  · have hcolneg : α.val = -β.val := by
      simpa only [hnegative, neg_one_smul] using hcol
    have hnegα : -α.val ∈ realization.positiveRoots := by
      rw [hcolneg, neg_neg]
      exact β.property
    exact False.elim (realization.positiveRoots_ne_neg α.property hnegα)

/-- Every Coxeter reflection belongs to a positive root. -/
theorem rootReflection_surjective : Function.Surjective realization.rootReflection := by
  intro t
  obtain ⟨w, i, ht⟩ := t.property
  have hxroot := realization.action_mem_roots w (realization.simpleRoot_mem_roots i)
  rcases realization.root_sign hxroot with hpos | hneg
  · refine ⟨⟨realization.action w (realization.simpleRoot i), hpos⟩, ?_⟩
    apply Subtype.ext
    apply realization.action_injective
    apply LinearEquiv.ext
    intro y
    rw [realization.rootReflection_apply, ht, realization.action_conjugate_simple]
  · refine ⟨⟨-realization.action w (realization.simpleRoot i), hneg⟩, ?_⟩
    apply Subtype.ext
    apply realization.action_injective
    apply LinearEquiv.ext
    intro y
    rw [realization.rootReflection_apply, ht, realization.action_conjugate_simple,
      LinearMap.BilinForm.neg_left]
    simp only [mul_neg, neg_smul, smul_neg, neg_neg]

/-- Positive roots and Coxeter reflections are in bijection. -/
noncomputable def rootReflectionEquiv :
    {x : V // x ∈ realization.positiveRoots} ≃ {t : W // cs.IsReflection t} :=
  Equiv.ofBijective realization.rootReflection
    ⟨realization.rootReflection_injective, realization.rootReflection_surjective⟩

/-- The reflection of a positive translated simple root is the conjugated simple generator. -/
theorem rootReflection_translated_simple (w : W) (i : Index)
    (hpos : realization.action w (realization.simpleRoot i) ∈ realization.positiveRoots) :
    (realization.rootReflection ⟨realization.action w (realization.simpleRoot i), hpos⟩).val =
      w * cs.simple i * w⁻¹ := by
  apply realization.action_injective
  apply LinearEquiv.ext
  intro y
  rw [realization.rootReflection_apply, realization.action_conjugate_simple]

private theorem inversionRoots_word_iff {word : List Index} (hred : cs.IsReduced word)
    (root : {x : V // x ∈ realization.positiveRoots}) :
    root.val ∈ realization.inversionRoots (cs.wordProd word) ↔
      (realization.rootReflection root).val ∈ cs.leftInvSeq word := by
  induction word using List.reverseRecOn with
  | nil =>
    simp only [cs.wordProd_nil, realization.inversionRoots_one, Set.mem_empty_iff_false,
      cs.leftInvSeq_nil, List.not_mem_nil]
  | append_singleton word i ih =>
    have hredword : cs.IsReduced word := by simpa using hred.take word.length
    have hascent : ¬ cs.IsRightDescent (cs.wordProd word) i := by
      rw [cs.not_isRightDescent_iff, hredword.eq]
      simpa only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
        List.length_singleton] using hred.eq
    have hnewpos := realization.action_simpleRoot_positive (cs.wordProd word) i hascent
    have hcompare : (realization.rootReflection root).val =
        cs.wordProd word * cs.simple i * (cs.wordProd word)⁻¹ ↔
        root.val = realization.action (cs.wordProd word) (realization.simpleRoot i) := by
      rw [← realization.rootReflection_translated_simple (cs.wordProd word) i hnewpos]
      constructor
      · intro heq
        have heq' : root =
            ⟨realization.action (cs.wordProd word) (realization.simpleRoot i), hnewpos⟩ :=
          realization.rootReflection_injective (Subtype.ext heq)
        exact congrArg Subtype.val heq'
      · intro heq
        have heq' : root =
            ⟨realization.action (cs.wordProd word) (realization.simpleRoot i), hnewpos⟩ :=
          Subtype.ext heq
        exact congrArg (fun α => (realization.rootReflection α).val) heq'
    rw [cs.wordProd_append, cs.wordProd_singleton,
      realization.inversionRoots_mul_simple (cs.wordProd word) i hascent, Set.mem_insert_iff]
    rw [← List.concat_eq_append, cs.leftInvSeq_concat]
    simp only [List.concat_eq_append, List.mem_append, List.mem_singleton]
    rw [← ih hredword, hcompare]
    exact or_comm

/-- A positive-root reflection is a left inversion exactly when its root is an inversion root. -/
theorem rootReflection_leftInversion_iff (w : W)
    (root : {x : V // x ∈ realization.positiveRoots}) :
    cs.IsLeftInversion w (realization.rootReflection root).val ↔
      root.val ∈ realization.inversionRoots w := by
  obtain ⟨word, hred, rfl⟩ := cs.exists_isReduced w
  exact (cs.mem_leftInvSeq_iff_isLeftInversion hred).symm.trans
    (inversionRoots_word_iff realization hred root).symm

/-- A positive-root reflection decreases length on the left exactly at its inversion roots. -/
theorem rootReflection_length_iff (w : W)
    (root : {x : V // x ∈ realization.positiveRoots}) :
    cs.length ((realization.rootReflection root).val * w) < cs.length w ↔
      root.val ∈ realization.inversionRoots w := by
  rw [← realization.rootReflection_leftInversion_iff]
  simp only [CoxeterSystem.IsLeftInversion, (realization.rootReflection root).property, true_and]

/-- A positive-root reflection decreases length on the right exactly when its root image
is negative. -/
theorem rootReflection_right_length (w : W)
    (root : {x : V // x ∈ realization.positiveRoots}) :
    cs.length (w * (realization.rootReflection root).val) < cs.length w ↔
      -realization.action w root.val ∈ realization.positiveRoots := by
  have hlen : cs.length (w * (realization.rootReflection root).val) =
      cs.length ((realization.rootReflection root).val * w⁻¹) := by
    rw [← cs.length_inv (w * (realization.rootReflection root).val), mul_inv_rev,
      (realization.rootReflection root).property.inv]
  rw [hlen, ← cs.length_inv w, realization.rootReflection_length_iff]
  change (root.val ∈ realization.positiveRoots ∧
    -realization.action (w⁻¹)⁻¹ root.val ∈ realization.positiveRoots) ↔
      -realization.action w root.val ∈ realization.positiveRoots
  simp only [inv_inv, root.property, true_and]

end BruhatIntervals.Realization
