import OrbitComplexity.BruhatIntervals.Realizations.Inversions

/-!
# Inversion roots of length-additive products

The inversion roots of a length-additive product are the disjoint union of the first factor's
inversion roots and its translates of the second factor's inversion roots. Reduced-word prefixes
preserve length additivity, and each new simple letter inserts one new positive root.

## Main results

* `Realization.inversionRoots_mul_of_length_add`: the disjoint inversion-root product formula.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Chapter VI, Section 1,
  Corollary 2 of Proposition 17.
-/

namespace BruhatIntervals.Realization

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private theorem inversions_word (u : W) {word : List Index} (hred : cs.IsReduced word)
    (hlength : cs.length (u * cs.wordProd word) = cs.length u + word.length) :
    Disjoint (realization.inversionRoots u)
      (realization.action u '' realization.inversionRoots (cs.wordProd word)) ∧
    realization.inversionRoots (u * cs.wordProd word) = realization.inversionRoots u ∪
      (realization.action u '' realization.inversionRoots (cs.wordProd word)) := by
  induction word using List.reverseRecOn with
  | nil => simp [realization.inversionRoots_one]
  | append_singleton word i ih =>
    have hprefix : cs.IsReduced word := by simpa using hred.take word.length
    have hlength' : cs.length ((u * cs.wordProd word) * cs.simple i) =
        cs.length u + word.length + 1 := by
      simpa only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
        List.length_singleton, mul_assoc, Nat.add_assoc] using hlength
    have hupper := cs.length_mul_le u (cs.wordProd word)
    rw [hprefix.eq] at hupper
    have hstep := cs.length_mul_le (u * cs.wordProd word) (cs.simple i)
    rw [cs.length_simple] at hstep
    have hadd : cs.length (u * cs.wordProd word) = cs.length u + word.length := by omega
    have hascent : ¬cs.IsRightDescent (u * cs.wordProd word) i :=
      cs.not_isRightDescent_iff.mpr (by omega)
    have hwordAscent : ¬cs.IsRightDescent (cs.wordProd word) i := by
      rw [cs.not_isRightDescent_iff, hprefix.eq]
      simpa only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
        List.length_singleton] using hred.eq
    obtain ⟨hdisjoint, hunion⟩ := ih hprefix hadd
    let newRoot := realization.action (u * cs.wordProd word) (realization.simpleRoot i)
    have hnew : newRoot ∉ realization.inversionRoots u := by
      intro hmem
      apply realization.action_root_not_inversions (u * cs.wordProd word) i
      rw [hunion]
      exact Or.inl hmem
    have himage : realization.action u ''
        realization.inversionRoots (cs.wordProd word * cs.simple i) =
          insert newRoot (realization.action u ''
            realization.inversionRoots (cs.wordProd word)) := by
      rw [realization.inversionRoots_mul_simple (cs.wordProd word) i hwordAscent,
        Set.image_insert_eq]
      congr 1
      dsimp only [newRoot]
      rw [map_mul, LinearEquiv.mul_apply]
    rw [cs.wordProd_append, cs.wordProd_singleton, himage, ← mul_assoc]
    constructor
    · apply Set.disjoint_left.mpr
      intro root hroot hinsert
      rcases Set.mem_insert_iff.mp hinsert with heq | hold
      · exact hnew (heq ▸ hroot)
      · exact Set.disjoint_left.mp hdisjoint hroot hold
    · rw [realization.inversionRoots_mul_simple (u * cs.wordProd word) i hascent, hunion]
      ext root
      simp only [Set.mem_insert_iff, Set.mem_union]
      tauto

/-- The inversion roots of a length-additive product are the disjoint union of the first
factor's inversion roots and the first factor's translate of the second factor's inversion roots. -/
theorem inversionRoots_mul_of_length_add (u v : W)
    (hlength : cs.length (u * v) = cs.length u + cs.length v) :
    Disjoint (realization.inversionRoots u)
      (realization.action u '' realization.inversionRoots v) ∧
    realization.inversionRoots (u * v) = realization.inversionRoots u ∪
      (realization.action u '' realization.inversionRoots v) := by
  obtain ⟨word, hred, hword⟩ := cs.exists_isReduced v
  rw [hword, hred.eq] at hlength
  rw [hword]
  exact inversions_word realization u hred hlength

end BruhatIntervals.Realization
