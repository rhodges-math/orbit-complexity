import OrbitComplexity.SchubertGeometry.Deodhar.Representatives
import OrbitComplexity.SchubertGeometry.Cells.Stability
import OrbitComplexity.SchubertGeometry.Deodhar.SimpleCell
import OrbitComplexity.SchubertGeometry.Deodhar.RankOnePoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupWeylQuotient
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBorelNormalizer


/-! # Signed prefix flags

The normalizer quotient identifies each signed prefix representative with its Weyl flag.
The proof compares the normalizer classes of the chosen signed simple factors.

## References

* R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Proposition 5.2.
-/

open BruhatIntervals ReductiveGroups SchubertGeometry
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def normalizerClass (g : G.points) (hg : g ∈ G.torusNormalizer) :
    G.torusNormalizer ⧸ G.torusInNormalizer :=
  QuotientGroup.mk ⟨g, hg⟩

omit [IsAlgClosed K] [CharZero K] in
private theorem class_mul (a b : G.points) (ha : a ∈ G.torusNormalizer)
    (hb : b ∈ G.torusNormalizer) :
    normalizerClass G (a * b) (G.torusNormalizer.mul_mem ha hb) =
      normalizerClass G a ha * normalizerClass G b hb := rfl

omit [IsAlgClosed K] [CharZero K] in
private theorem class_congr {a b : G.points} (ha : a ∈ G.torusNormalizer)
    (hb : b ∈ G.torusNormalizer) (h : a = b) :
    normalizerClass G a ha = normalizerClass G b hb := by
  subst b
  rfl

private theorem class_of_flag_eq (a : G.points) (ha : a ∈ G.torusNormalizer)
    (w : G.weylGroup) (hf : flagProjection G a = flagProjection G (G.weylPoint w)) :
    normalizerClass G a ha = G.weylQuotientMap w := by
  apply QuotientGroup.eq.mpr
  change a⁻¹ * G.weylPoint w ∈ G.torusPoints
  have h : a⁻¹ * G.weylPoint w ∈ G.borelPoints ⊓ G.torusNormalizer :=
    ⟨(flagProjection_eq_iff G _ _).mp hf,
      G.torusNormalizer.mul_mem (G.torusNormalizer.inv_mem ha) (G.weylPoint_mem_normalizer w)⟩
  rwa [G.borel_inf_torus_normalizer] at h

private theorem simple_class (i : G.rootBase.support) :
    normalizerClass G (G.reflectionPoint i.val) (G.isBruhatSystem.weyl.mem_normalizer i.val) =
      G.weylQuotientMap (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  have hf := flag_reflection_eq_inv G i 1
  simp only [one_mul] at hf
  exact class_of_flag_eq G _ _ _ (hf.trans (simpleRepresentative_flag G i))

private theorem representative_class (i : G.rootBase.support) :
    normalizerClass G (simpleRepresentative G i)
      (G.torusNormalizer.inv_mem (G.isBruhatSystem.weyl.mem_normalizer i.val)) =
      G.weylQuotientMap (RootPairing.weylGroup.ofIdx G.rootSystem i.val) :=
  class_of_flag_eq G _ _ _ (simpleRepresentative_flag G i)

variable {word : List G.rootBase.support} (expression : Subexpression word)

private theorem step_normalizer (j : Fin word.length) :
    subwordStepPoint G expression j ∈ G.torusNormalizer := by
  classical
  unfold subwordStepPoint simpleRepresentative
  simp only [inv_inv]
  split
  · exact G.isBruhatSystem.weyl.mem_normalizer _
  · split
    · exact G.torusNormalizer.one_mem
    · exact G.torusNormalizer.inv_mem (G.isBruhatSystem.weyl.mem_normalizer _)

private theorem equal_iff_choice {S W : Type*} [Group W] {M : CoxeterMatrix S}
    (cs : CoxeterSystem M W) {word : List S} (expression : Subexpression word)
    (j : Fin word.length) : j ∈ equalSteps cs expression ↔
      expression.choices[j.val]'(by rw [expression.length_choices]; exact j.isLt) = false := by
  have hsimple : cs.simple (word[j.val]) ≠ 1 := by
    intro h
    have hlen := congrArg cs.length h
    exact Nat.one_ne_zero (by simpa only [cs.length_simple, cs.length_one] using hlen)
  change expression.prefixProd cs j.val = expression.prefixProd cs (j.val + 1) ↔ _
  rw [expression.prefixProd_succ cs j]
  cases hc : expression.choices[j.val]'(by rw [expression.length_choices]; exact j.isLt)
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
  · simp only [↓reduceIte, Bool.true_eq_false, iff_false]
    intro h
    apply hsimple
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)

private def chosenFactor (j : Fin word.length) : G.weylGroup :=
  if expression.choices[j.val]'(by rw [expression.length_choices]; exact j.isLt) then
    RootPairing.weylGroup.ofIdx G.rootSystem (word[j.val] : G.rootIndex) else 1

private theorem step_eq_reflection (j : Fin word.length)
    (hn : j ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression) :
    subwordStepPoint G expression j = G.reflectionPoint (word[j.val] : G.rootIndex) := by
  classical
  simp only [subwordStepPoint, simpleRepresentative, hn, ↓reduceIte, inv_inv]

private theorem step_eq_one (j : Fin word.length)
    (hn : j ∉ negativeSteps (weylCoxeterSystem G.rootBase) expression)
    (he : j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression) :
    subwordStepPoint G expression j = 1 := by
  classical
  simp only [subwordStepPoint, hn, he, ↓reduceIte]

private theorem step_eq_inverse (j : Fin word.length) (i : G.rootBase.support)
    (hi : word[j.val] = i) (hn : j ∉ negativeSteps (weylCoxeterSystem G.rootBase) expression)
    (he : j ∉ equalSteps (weylCoxeterSystem G.rootBase) expression) :
    subwordStepPoint G expression j = simpleRepresentative G i := by
  classical
  simp only [subwordStepPoint, hn, he, ↓reduceIte, hi]

private theorem factor_eq_simple (j : Fin word.length)
    (hc : expression.choices[j.val]'(by rw [expression.length_choices]; exact j.isLt) = true) :
    chosenFactor G expression j =
      RootPairing.weylGroup.ofIdx G.rootSystem (word[j.val] : G.rootIndex) := by
  simp only [chosenFactor, hc, ↓reduceIte]

private theorem factor_eq_one (j : Fin word.length)
    (hc : expression.choices[j.val]'(by rw [expression.length_choices]; exact j.isLt) = false) :
    chosenFactor G expression j = 1 := by
  simp only [chosenFactor, hc, Bool.false_eq_true, ↓reduceIte]

set_option maxHeartbeats 400000 in
private theorem step_class (j : Fin word.length) :
    normalizerClass G (subwordStepPoint G expression j) (step_normalizer G expression j) =
      G.weylQuotientMap (chosenFactor G expression j) := by
  classical
  let i : G.rootBase.support := word[j.val]
  have heq := equal_iff_choice (weylCoxeterSystem G.rootBase) expression j
  by_cases hn : j ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression
  · have hc : expression.choices[j.val]'(by
        rw [expression.length_choices]; exact j.isLt) = true := by
      apply Bool.eq_true_of_not_eq_false
      exact fun hf => hn.2 (heq.mpr hf).symm
    have hp := step_eq_reflection G expression j hn
    have hf := factor_eq_simple G expression j hc
    exact (class_congr G (step_normalizer G expression j)
      (G.isBruhatSystem.weyl.mem_normalizer i.val) hp).trans
      ((simple_class G i).trans (congrArg (fun a : G.weylGroup => G.weylQuotientMap a) hf.symm))
  · by_cases he : j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression
    · have hc := heq.mp he
      have hp := step_eq_one G expression j hn he
      have hf := factor_eq_one G expression j hc
      exact (class_congr G (step_normalizer G expression j) G.torusNormalizer.one_mem hp).trans
        ((show normalizerClass G 1 G.torusNormalizer.one_mem = 1 from rfl).trans
          ((map_one G.weylQuotientMap).symm.trans
          (congrArg (fun a : G.weylGroup => G.weylQuotientMap a) hf.symm)))
    · have hc : expression.choices[j.val]'(by
          rw [expression.length_choices]; exact j.isLt) = true := by
        apply Bool.eq_true_of_not_eq_false
        exact fun hf => he (heq.mpr hf)
      have hp := step_eq_inverse G expression j i rfl hn he
      have hf := factor_eq_simple G expression j hc
      have hs := representative_class G i
      exact (class_congr G (step_normalizer G expression j)
        (G.torusNormalizer.inv_mem (G.isBruhatSystem.weyl.mem_normalizer i.val)) hp).trans
        (hs.trans (congrArg (fun a : G.weylGroup => G.weylQuotientMap a) hf.symm))

private theorem chosenFactor_list : List.ofFn (chosenFactor G expression) =
    expression.factors (weylCoxeterSystem G.rootBase) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, expression.length_factors]
  · intro j hj hk
    simp only [List.getElem_ofFn, Subexpression.factors, List.getElem_map,
      List.getElem_zip, chosenFactor, weylCoxeterSystem_simple]

private theorem list_normalizer (l : List (Fin word.length)) :
    (l.map (subwordStepPoint G expression)).prod ∈ G.torusNormalizer := by
  apply Subgroup.list_prod_mem
  intro a ha
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
  exact step_normalizer G expression j

private theorem list_class (l : List (Fin word.length)) :
    normalizerClass G (l.map (subwordStepPoint G expression)).prod
      (list_normalizer G expression l) =
      G.weylQuotientMap (l.map (chosenFactor G expression)).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, map_one]; rfl
  | cons j l ih =>
    have hq := class_mul G (subwordStepPoint G expression j)
      (l.map (subwordStepPoint G expression)).prod (step_normalizer G expression j)
      (list_normalizer G expression l)
    have hm := congrArg₂ (fun a b => a * b) (step_class G expression j) ih
    exact hq.trans (hm.trans (map_mul G.weylQuotientMap _ _).symm)

/-- A signed prefix representative has the flag of the corresponding subexpression prefix. -/
theorem subwordRepresentative_flag (n : ℕ) :
    flagProjection G (subwordRepresentative G expression n) =
      flagProjection G (G.weylPoint
        (expression.prefixProd (weylCoxeterSystem G.rootBase) n)) := by
  have h := list_class G expression ((List.finRange word.length).take n)
  simp only [List.map_take, ← List.ofFn_eq_map, chosenFactor_list] at h
  have h' : QuotientGroup.mk (⟨subwordRepresentative G expression n,
      subwordRepresentative_mem_normalizer G expression n⟩ : G.torusNormalizer) =
      QuotientGroup.mk (⟨G.weylPoint
        (expression.prefixProd (weylCoxeterSystem G.rootBase) n),
          G.weylPoint_mem_normalizer _⟩ : G.torusNormalizer) := h
  have ht : (⟨subwordRepresentative G expression n,
      subwordRepresentative_mem_normalizer G expression n⟩ : G.torusNormalizer)⁻¹ *
      ⟨G.weylPoint (expression.prefixProd (weylCoxeterSystem G.rootBase) n),
        G.weylPoint_mem_normalizer _⟩ ∈ G.torusInNormalizer := QuotientGroup.eq.mp h'
  exact (flagProjection_eq_iff G _ _).mpr (G.torus_le_borel ht)


end
end SchubertGeometry
