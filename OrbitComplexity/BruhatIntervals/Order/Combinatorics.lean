import OrbitComplexity.BruhatIntervals.Order.Descents
import OrbitComplexity.BruhatIntervals.Order.Interval
import OrbitComplexity.BruhatIntervals.Words.Parabolic
import OrbitComplexity.BruhatIntervals.Words.Support
import OrbitComplexity.BruhatIntervals.Realizations.RootSets

/-!
# Coxeter combinatorial foundations

Length, reduced expressions, parabolic representatives and factorizations, support, descents,
root inversions, and Bruhat intervals satisfy their usual defining properties. The root inversion
sets are finite and count length in arbitrary Coxeter systems.

## Main results

* `coxeter_combinatorics`: the complete defining properties of Coxeter combinatorial data.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Chapters 1, 2, and 4.
-/

namespace BruhatIntervals

/-- Coxeter length, parabolic representatives, support, descents, root inversions, and Bruhat
intervals have their defining properties, including both inversion cardinalities and the
geometric and reflection descriptions of left inversions. -/
theorem coxeter_combinatorics :
  ∀ {S : Type*} {W : Type*} {V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V)),
    (∀ word : List S, cs.IsReduced word ↔ cs.length (cs.wordProd word) = word.length) ∧
    (∀ w : W, ∃ word : List S, cs.wordProd word = w ∧ word.length = cs.length w ∧
      ∀ other : List S, cs.wordProd other = w → cs.length w ≤ other.length) ∧
    (∀ a b : List S, cs.IsReduced a → cs.IsReduced b →
      (cs.IsReduced (a ++ b) ↔ cs.length (cs.wordProd a * cs.wordProd b) =
        cs.length (cs.wordProd a) + cs.length (cs.wordProd b))) ∧
    (∀ (indices : Set S) (w : W),
      (cs.IsMinimalCosetRep indices w ↔
        ∀ a ∈ cs.parabolic indices, cs.length w ≤ cs.length (w * a)) ∧
      (cs.IsMinimalCosetRep indices w ↔ ∀ i ∈ indices, i ∉ rightDescents cs w)) ∧
    (∀ (indices : Set S) (w : W),
      (IsMinimalLeftRep cs indices w ↔
        ∀ a ∈ cs.parabolic indices, cs.length w ≤ cs.length (a * w)) ∧
      (IsMinimalLeftRep cs indices w ↔ ∀ i ∈ indices, i ∉ leftDescents cs w)) ∧
    (∀ (indices : Set S) (w : W), ∃! factors : W × W,
      cs.IsMinimalCosetRep indices factors.1 ∧ factors.2 ∈ cs.parabolic indices ∧
      w = factors.1 * factors.2 ∧
      cs.length w = cs.length factors.1 + cs.length factors.2) ∧
    (∀ (indices : Set S) (w : W), ∃! factors : W × W,
      factors.1 ∈ cs.parabolic indices ∧ IsMinimalLeftRep cs indices factors.2 ∧
      w = factors.1 * factors.2 ∧
      cs.length w = cs.length factors.1 + cs.length factors.2) ∧
    (∀ (w : W) (word : List S), cs.IsReduced word → cs.wordProd word = w →
      support cs w = {t | t ∈ word.map cs.simple}) ∧
    (∀ w : W, (support cs w).Finite ∧ supportCard cs w = (support cs w).ncard) ∧
    (∀ (w : W) (i : S),
      (i ∈ leftDescents cs w ↔ cs.length (cs.simple i * w) < cs.length w) ∧
      (i ∈ rightDescents cs w ↔ cs.length (w * cs.simple i) < cs.length w)) ∧
    (∀ (w : W) (root : V),
      (root ∈ realization.inversionRoots w ↔ root ∈ realization.positiveRoots ∧
        -realization.action w⁻¹ root ∈ realization.positiveRoots) ∧
      (root ∈ realization.rightInversionRoots w ↔ root ∈ realization.positiveRoots ∧
        -realization.action w root ∈ realization.positiveRoots)) ∧
    (∀ w : W, (realization.inversionRoots w).Finite ∧
      (realization.rightInversionRoots w).Finite ∧
      (realization.inversionRoots w).ncard = cs.length w ∧
      (realization.rightInversionRoots w).ncard = cs.length w) ∧
    (∀ w : W, realization.inversionRoots w = realization.positiveRoots ∩
      (realization.action w '' (Neg.neg '' realization.positiveRoots)) ∧
      realization.inversionRoots w = {root : V | ∃ h : root ∈ realization.positiveRoots,
        cs.length ((realization.rootReflection ⟨root, h⟩).val * w) < cs.length w}) ∧
    (∀ u v : W, cs.BruhatLE u v ↔ Relation.ReflTransGen
      (fun x y : W => ∃ root : {a : V // a ∈ realization.positiveRoots},
        y = x * (realization.rootReflection root).val ∧ cs.length x < cs.length y) u v) ∧
    (∀ u v w : W, (w ∈ bruhatInterval cs u v ↔ cs.BruhatLE u w ∧ cs.BruhatLE w v) ∧
      (bruhatInterval cs u v).Finite) := by
  intro S W V _ M cs _ _ realization
  refine ⟨?_, ?_, ?_, ?_, ?_, right_parabolic_decomposition cs,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro word
    rfl
  · intro w
    obtain ⟨word, hred, hword⟩ := cs.exists_isReduced w
    refine ⟨word, hword.symm, ?_, ?_⟩
    · rw [hword, hred.eq]
    · intro other hother
      rw [← hother]
      exact cs.length_wordProd_le other
  · intro a b ha hb
    change cs.length (cs.wordProd (a ++ b)) = (a ++ b).length ↔ _
    rw [cs.wordProd_append, List.length_append, ← ha.eq, ← hb.eq]
  · intro indices w
    exact ⟨Iff.rfl, cs.isMinimalCosetRep_iff⟩
  · intro indices w
    exact ⟨Iff.rfl, isMinimalLeftRep_iff cs⟩
  · intro indices w
    obtain ⟨factors, hf, huniq⟩ := left_parabolic_decomposition cs indices w
    refine ⟨factors, ⟨hf.1, (isMinimalLeftRep_iff cs).mpr hf.2.1, hf.2.2⟩, ?_⟩
    intro other hother
    exact huniq other ⟨hother.1, (isMinimalLeftRep_iff cs).mp hother.2.1, hother.2.2⟩
  · intro w word hred hword
    exact support_eq_letters cs hred hword
  · intro w
    exact ⟨support_finite cs w, rfl⟩
  · intro w i
    exact ⟨mem_leftDescents cs w i, mem_rightDescents cs w i⟩
  · intro w root
    exact ⟨Iff.rfl, realization.mem_rightInversionRoots w root⟩
  · intro w
    exact ⟨realization.inversionRoots_finite w, realization.rightInversionRoots_finite w,
      realization.inversionRoots_ncard w, realization.rightInversionRoots_ncard w⟩
  · intro w
    exact ⟨realization.inversionRoots_eq_image w, realization.inversionRoots_eq_reflections w⟩
  · intro u v
    rw [bruhatLE_iff_right_steps cs]
    have heq : RightBruhatStep cs = fun x y : W =>
        ∃ root : {a : V // a ∈ realization.positiveRoots},
          y = x * (realization.rootReflection root).val ∧ cs.length x < cs.length y := by
      funext x y
      apply propext
      constructor
      · rintro ⟨t, ht, hprod, hlength⟩
        obtain ⟨root, hroot⟩ := realization.rootReflection_surjective ⟨t, ht⟩
        have hval := congrArg Subtype.val hroot
        exact ⟨root, by simpa only [hval] using hprod, hlength⟩
      · rintro ⟨root, hprod, hlength⟩
        exact ⟨(realization.rootReflection root).val,
          (realization.rootReflection root).property, hprod, hlength⟩
    rw [heq]
  · intro u v w
    exact ⟨mem_bruhatInterval cs, bruhatInterval_finite cs u v⟩

end BruhatIntervals
