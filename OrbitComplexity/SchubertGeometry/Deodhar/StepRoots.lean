import OrbitComplexity.ReductiveGroups.Groups.Cells.BruhatDoubleCosets
import OrbitComplexity.BruhatIntervals.Words.Subexpression

/-! # Root signs at subexpression steps

The Bruhat direction of a chosen step determines the sign of the transported simple root.
Distinguished omitted steps also transport the simple root to a positive root.
-/
open BruhatIntervals ReductiveGroups
namespace SchubertGeometry
noncomputable section

section Signs
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Fintype ι] [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) {word : List b.support} (expression : Subexpression word)

private theorem next_of_ne (j : Fin word.length)
    (hne : expression.prefixProd (weylCoxeterSystem b) j.val ≠
      expression.prefixProd (weylCoxeterSystem b) (j.val + 1)) :
    expression.prefixProd (weylCoxeterSystem b) (j.val + 1) =
      expression.prefixProd (weylCoxeterSystem b) j.val *
        RootPairing.weylGroup.ofIdx P (word[j.val] : ι) := by
  have h := expression.prefixProd_succ (weylCoxeterSystem b) j
  split at h
  · simpa only [weylCoxeterSystem_simple] using h
  · simp only [mul_one] at h
    exact False.elim (hne h.symm)

/-- An increasing subexpression step transports its simple root to a positive root. -/
theorem positiveStep_root (j : Fin word.length)
    (hj : j ∈ positiveSteps (weylCoxeterSystem b) expression) :
    b.IsPos (P.weylGroupToPerm
      (expression.prefixProd (weylCoxeterSystem b) j.val) (word.get j).val) := by
  have hlt := hj.1.length_lt_of_ne hj.2
  rw [next_of_ne b expression j hj.2] at hlt
  have hdich := (weylCoxeterSystem b).length_mul_simple
    (expression.prefixProd (weylCoxeterSystem b) j.val) word[j.val]
  simp only [weylCoxeterSystem_simple] at hdich
  have hlen := hdich.resolve_right (by omega)
  apply isPos_of_length_mul_simple b _ (word.get j)
  simpa only [weylCoxeterSystem_simple, List.get_eq_getElem] using hlen

/-- A decreasing subexpression step transports its simple root to a negative root. -/
theorem negativeStep_root (j : Fin word.length)
    (hj : j ∈ negativeSteps (weylCoxeterSystem b) expression) :
    ¬ b.IsPos (P.weylGroupToPerm
      (expression.prefixProd (weylCoxeterSystem b) j.val) (word.get j).val) := by
  intro hpos
  have hlt := hj.1.length_lt_of_ne hj.2
  rw [next_of_ne b expression j hj.2.symm, weylCoxeterSystem_length,
    weylCoxeterSystem_length] at hlt
  have hc := rootInversionCount_mul_simple_of_pos b
    (expression.prefixProd (weylCoxeterSystem b) j.val) (word.get j) hpos
  simp only [List.get_eq_getElem] at hc
  omega

/-- A distinguished omitted step transports its simple root to a positive root. -/
theorem equalStep_root (hd : IsDistinguished (weylCoxeterSystem b) expression)
    (j : Fin word.length) (hj : j ∈ equalSteps (weylCoxeterSystem b) expression) :
    b.IsPos (P.weylGroupToPerm
      (expression.prefixProd (weylCoxeterSystem b) j.val) (word.get j).val) := by
  have hle := (hd j).length_le
  change expression.prefixProd (weylCoxeterSystem b) j.val =
    expression.prefixProd (weylCoxeterSystem b) (j.val + 1) at hj
  rw [← hj] at hle
  have hdich := (weylCoxeterSystem b).length_mul_simple
    (expression.prefixProd (weylCoxeterSystem b) j.val) word[j.val]
  have hlen := hdich.resolve_right (by omega)
  apply isPos_of_length_mul_simple b _ (word.get j)
  simpa only [weylCoxeterSystem_simple, List.get_eq_getElem] using hlen
end Signs

end
end SchubertGeometry
