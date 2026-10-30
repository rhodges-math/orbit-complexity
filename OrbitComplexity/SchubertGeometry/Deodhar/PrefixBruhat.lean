import OrbitComplexity.SchubertGeometry.Deodhar.Elements
import OrbitComplexity.SchubertGeometry.Deodhar.PrefixCharts
import OrbitComplexity.ReductiveGroups.Groups.Cells.BruhatDoubleCosets

/-! # Bruhat double cosets of signed parameter prefixes

Every signed factor with a nonzero omitted coordinate lies in its simple Bruhat double coset.
Ascending multiplication along a reduced word then determines every prefix double coset.
-/

open BruhatIntervals ReductiveGroups
open scoped Pointwise
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word) (p : Fin word.length → K)

attribute [local irreducible] deodharStep deodharPrefix gaParameterPoint

private theorem simpleCoset_eq (i : G.rootBase.support) :
    subgroupDoubleCoset G.borelPoints (G.reflectionPoint i.val) =
      subgroupDoubleCoset G.borelPoints
        (G.weylPoint (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) := by
  simpa only [G.weylPoint_eq] using G.isBruhatSystem.doubleCoset_simple_eq i

private theorem positiveFactor_mem (i : G.rootBase.support) (t : K) :
    gaParameterPoint (G.simpleRootMap i) t * G.reflectionPoint i.val ∈
      subgroupDoubleCoset G.borelPoints (G.reflectionPoint i.val) :=
  mul_mem_subgroupDoubleCoset (mem_subgroupDoubleCoset_self _ _)
    ((G.isBruhatSystem.rankOne i).x_mem t)

private theorem negativeFactor_mem (i : G.rootBase.support) (t : K) (ht : t ≠ 0) :
    gaParameterPoint (G.negativeSimpleRootMap i) t ∈
      subgroupDoubleCoset G.borelPoints (G.reflectionPoint i.val) :=
  (G.isBruhatSystem.rankOne i).y_mem_doubleCoset ht

private theorem inverseFactor_mem (i : G.rootBase.support) :
    (G.reflectionPoint i.val)⁻¹ ∈
      subgroupDoubleCoset G.borelPoints (G.reflectionPoint i.val) :=
  (G.isBruhatSystem.rankOne i).inv_mem_doubleCoset

private theorem signedStep_negative (j : Fin word.length)
    (hn : j ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression) :
    deodharStep G expression p j ∈ subgroupDoubleCoset G.borelPoints
      (G.reflectionPoint (word.get j).val) := by
  classical
  let i : G.rootBase.support := word.get j
  change deodharStep G expression p j ∈ subgroupDoubleCoset G.borelPoints
    (G.reflectionPoint i.val)
  have h : deodharStep G expression p j =
      gaParameterPoint (G.simpleRootMap i) (p j) * G.reflectionPoint i.val := by
    simp only [i, List.get_eq_getElem, deodharStep, deodharRootElement, subwordStepPoint,
      hn, ↓reduceIte,
      simpleRepresentative, inv_inv]
  exact (congrArg (fun g : G.points => g ∈ subgroupDoubleCoset G.borelPoints
    (G.reflectionPoint i.val)) h).mpr (positiveFactor_mem G i (p j))

private theorem signedStep_equal (j : Fin word.length)
    (hn : j ∉ negativeSteps (weylCoxeterSystem G.rootBase) expression)
    (he : j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression) (hp : p j ≠ 0) :
    deodharStep G expression p j ∈ subgroupDoubleCoset G.borelPoints
      (G.reflectionPoint (word.get j).val) := by
  classical
  let i : G.rootBase.support := word.get j
  change deodharStep G expression p j ∈ subgroupDoubleCoset G.borelPoints
    (G.reflectionPoint i.val)
  have h : deodharStep G expression p j =
      gaParameterPoint (G.negativeSimpleRootMap i) (p j) := by
    simp only [i, List.get_eq_getElem, deodharStep, deodharRootElement, subwordStepPoint,
      hn, he, ↓reduceIte,
      mul_one]
  exact (congrArg (fun g : G.points => g ∈ subgroupDoubleCoset G.borelPoints
    (G.reflectionPoint i.val)) h).mpr (negativeFactor_mem G i (p j) hp)

private theorem signedStep_positive (j : Fin word.length)
    (hn : j ∉ negativeSteps (weylCoxeterSystem G.rootBase) expression)
    (he : j ∉ equalSteps (weylCoxeterSystem G.rootBase) expression) :
    deodharStep G expression p j ∈ subgroupDoubleCoset G.borelPoints
      (G.reflectionPoint (word.get j).val) := by
  classical
  let i : G.rootBase.support := word.get j
  change deodharStep G expression p j ∈ subgroupDoubleCoset G.borelPoints
    (G.reflectionPoint i.val)
  have h : deodharStep G expression p j = (G.reflectionPoint i.val)⁻¹ := by
    simp only [i, List.get_eq_getElem, deodharStep, deodharRootElement, subwordStepPoint,
      hn, he, ↓reduceIte,
      one_mul, simpleRepresentative]
  exact (congrArg (fun g : G.points => g ∈ subgroupDoubleCoset G.borelPoints
    (G.reflectionPoint i.val)) h).mpr (inverseFactor_mem G i)

private theorem signedStep_mem (j : Fin word.length)
    (hp : j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression → p j ≠ 0) :
    deodharStep G expression p j ∈ subgroupDoubleCoset G.borelPoints
      (G.reflectionPoint (word.get j).val) := by
  classical
  by_cases hn : j ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression
  · exact signedStep_negative G expression p j hn
  · by_cases he : j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression
    · exact signedStep_equal G expression p j hn he (hp he)
    · exact signedStep_positive G expression p j hn he

private theorem prefix_succ (j : Fin word.length) :
    deodharPrefix G expression p (j.val + 1) =
      deodharPrefix G expression p j.val * deodharStep G expression p j := by
  unfold deodharPrefix
  rw [List.prod_take_succ _ _ (by simpa only [List.length_ofFn] using j.isLt),
    List.getElem_ofFn]

private theorem word_succ (n : ℕ) (hn : n < word.length) :
    simpleWeylWord G.rootBase (word.take (n + 1)) =
      simpleWeylWord G.rootBase (word.take n) *
        RootPairing.weylGroup.ofIdx G.rootSystem (word[n]'hn).val := by
  rw [List.take_succ_eq_append_getElem hn, simpleWeylWord_append]
  simp only [simpleWeylWord, mul_one]

/-- A signed parameter prefix of a reduced word lies in its full-word Bruhat double coset. -/
theorem deodharPrefix_mem_doubleCoset
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hp : ∀ j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression, p j ≠ 0)
    (n : ℕ) : n ≤ word.length →
    deodharPrefix G expression p n ∈ subgroupDoubleCoset G.borelPoints
      (G.weylPoint (simpleWeylWord G.rootBase (word.take n))) := by
  induction n with
  | zero =>
    intro _
    simp only [deodharPrefix, List.take_zero, List.prod_nil]
    change 1 ∈ subgroupDoubleCoset G.borelPoints (G.weylPoint 1)
    rw [G.weylPoint_eq, weylElementPoint_one]
    exact mem_subgroupDoubleCoset_self _ _
  | succ n ih =>
    intro hn
    have hlt : n < word.length := Nat.lt_of_succ_le hn
    have ha := wordCell_ascent G word hred n hlt
    have hm : subgroupDoubleCoset G.borelPoints
        (G.weylPoint (simpleWeylWord G.rootBase (word.take n))) *
        subgroupDoubleCoset G.borelPoints
          (G.weylPoint (RootPairing.weylGroup.ofIdx G.rootSystem (word[n]'hlt).val)) =
        subgroupDoubleCoset G.borelPoints
          (G.weylPoint (simpleWeylWord G.rootBase (word.take n) *
            RootPairing.weylGroup.ofIdx G.rootSystem (word[n]'hlt).val)) := by
      simpa only [G.weylPoint_eq] using
        G.isBruhatSystem.doubleCoset_mul_eq_of_isPos
          (simpleWeylWord G.rootBase (word.take n)) (word[n]'hlt) ha
    rw [word_succ G n hlt, prefix_succ G expression p ⟨n, hlt⟩, ← hm]
    refine ⟨_, ih (Nat.le_of_succ_le hn), _, ?_, rfl⟩
    rw [← simpleCoset_eq G (word[n]'hlt)]
    exact signedStep_mem G expression p ⟨n, hlt⟩ (hp ⟨n, hlt⟩)

end SchubertGeometry
