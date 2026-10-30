import OrbitComplexity.SchubertGeometry.Deodhar.Elements
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupReducedWords

/-! # Signed subword products are Weyl representatives

For a subexpression of a word, the product of the signed simple representatives along a prefix
is the representative `u̇` of the prefix's Weyl element `u`, that is, the product of the simple
representatives `ṡᵢ` along any reduced word for `u`.

## Main results

* `SchubertGeometry.subwordRepresentative_eq_weylElement`: the signed prefix product is the
  representative of its Weyl element.

## References

* R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Representation Theory 8 (2004),
  212–242, proof of Proposition 5.2.
-/

namespace SchubertGeometry
noncomputable section
open BruhatIntervals ReductiveGroups
universe u

section Words

variable {ι R M₀ N₀ : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₀] [Module R N₀]
  {P : RootPairing ι R M₀ N₀} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base) {Γ : Type*} [Group Γ] (f : ι → Γ)

/-- With reduced-word independence, a length-increasing simple reflection multiplies the
representative by its simple representative. -/
private theorem point_mul_simple
    (hind : ∀ l k : List b.support, (weylCoxeterSystem b).IsReduced l →
      (weylCoxeterSystem b).IsReduced k → simpleWeylWord b l = simpleWeylWord b k →
        simpleWordPoint f b l = simpleWordPoint f b k)
    (w : P.weylGroup) (s : b.support)
    (hlen : (weylCoxeterSystem b).length (w * (weylCoxeterSystem b).simple s) =
      (weylCoxeterSystem b).length w + 1) :
    weylElementPoint f b (w * (weylCoxeterSystem b).simple s) =
      weylElementPoint f b w * f (s : ι) := by
  have hw := chosenReducedWord_isReduced b w
  have hprod : simpleWeylWord b (chosenReducedWord b w ++ [s]) =
      w * (weylCoxeterSystem b).simple s := by
    rw [simpleWeylWord_append_singleton, simpleWeylWord_chosenReducedWord,
      weylCoxeterSystem_simple]
  have hred : (weylCoxeterSystem b).IsReduced (chosenReducedWord b w ++ [s]) := by
    change (weylCoxeterSystem b).length
      ((weylCoxeterSystem b).wordProd (chosenReducedWord b w ++ [s])) =
        (chosenReducedWord b w ++ [s]).length
    rw [weylCoxeterSystem_wordProd, hprod, hlen, List.length_append, List.length_singleton,
      ← hw.eq, weylCoxeterSystem_wordProd, simpleWeylWord_chosenReducedWord]
  have h := hind (chosenReducedWord b (w * (weylCoxeterSystem b).simple s))
    (chosenReducedWord b w ++ [s]) (chosenReducedWord_isReduced b _) hred
    (by rw [simpleWeylWord_chosenReducedWord, hprod])
  rw [weylElementPoint, h, simpleWordPoint_append, simpleWordPoint_singleton, weylElementPoint]

/-- With reduced-word independence, at a right descent the simple reflection multiplies the
representative by the inverse of its simple representative. -/
private theorem point_mul_simple_of_descent
    (hind : ∀ l k : List b.support, (weylCoxeterSystem b).IsReduced l →
      (weylCoxeterSystem b).IsReduced k → simpleWeylWord b l = simpleWeylWord b k →
        simpleWordPoint f b l = simpleWordPoint f b k)
    (w : P.weylGroup) (s : b.support) (hdesc : (weylCoxeterSystem b).IsRightDescent w s) :
    weylElementPoint f b (w * (weylCoxeterSystem b).simple s) =
      weylElementPoint f b w * (f (s : ι))⁻¹ := by
  have hlen := (weylCoxeterSystem b).isRightDescent_iff.mp hdesc
  have h := point_mul_simple b f hind (w * (weylCoxeterSystem b).simple s) s (by
    rw [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one]
    exact hlen.symm)
  rw [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one] at h
  rw [h, mul_inv_cancel_right]

/-- With reduced-word independence, the ordered product of signed steps along a subexpression
prefix is the representative of the prefix's Weyl element. -/
private theorem step_prod_eq
    (hind : ∀ l k : List b.support, (weylCoxeterSystem b).IsReduced l →
      (weylCoxeterSystem b).IsReduced k → simpleWeylWord b l = simpleWeylWord b k →
        simpleWordPoint f b l = simpleWordPoint f b k)
    {word : List b.support} (expression : Subexpression word) (step : Fin word.length → Γ)
    (hneg : ∀ j ∈ negativeSteps (weylCoxeterSystem b) expression,
      step j = (f (word[j.val] : ι))⁻¹)
    (heq : ∀ j ∈ equalSteps (weylCoxeterSystem b) expression, step j = 1)
    (hpos : ∀ j, j ∉ negativeSteps (weylCoxeterSystem b) expression →
      j ∉ equalSteps (weylCoxeterSystem b) expression → step j = f (word[j.val] : ι))
    (n : ℕ) :
    ((List.ofFn step).take n).prod =
      weylElementPoint f b (expression.prefixProd (weylCoxeterSystem b) n) := by
  induction n with
  | zero =>
    rw [Subexpression.prefixProd_zero, weylElementPoint_one, List.take_zero, List.prod_nil]
  | succ n ih =>
    by_cases hn : n < word.length
    · have hs : expression.prefixProd (weylCoxeterSystem b) (n + 1) =
          expression.prefixProd (weylCoxeterSystem b) n *
            (if expression.choices[n]'(by rw [expression.length_choices]; exact hn)
              then (weylCoxeterSystem b).simple word[n] else 1) :=
        expression.prefixProd_succ (weylCoxeterSystem b) ⟨n, hn⟩
      rw [List.prod_take_succ _ _ (by rw [List.length_ofFn]; exact hn), List.getElem_ofFn, ih]
      split at hs
      · by_cases hdesc : (weylCoxeterSystem b).IsRightDescent
            (expression.prefixProd (weylCoxeterSystem b) n) word[n]
        · have hle := ((weylCoxeterSystem b).bruhatStep_mul_simple_of_isRightDescent _
            hdesc).bruhatLE
          have hlen := (weylCoxeterSystem b).isRightDescent_iff.mp hdesc
          have hne : expression.prefixProd (weylCoxeterSystem b) n *
              (weylCoxeterSystem b).simple word[n] ≠
                expression.prefixProd (weylCoxeterSystem b) n := by
            intro h
            rw [h] at hlen
            omega
          have hmem : (⟨n, hn⟩ : Fin word.length) ∈
              negativeSteps (weylCoxeterSystem b) expression := by
            show (weylCoxeterSystem b).BruhatLE
                (expression.prefixProd (weylCoxeterSystem b) (n + 1))
                (expression.prefixProd (weylCoxeterSystem b) n) ∧
              expression.prefixProd (weylCoxeterSystem b) (n + 1) ≠
                expression.prefixProd (weylCoxeterSystem b) n
            rw [hs]
            exact ⟨hle, hne⟩
          rw [hneg _ hmem, hs, point_mul_simple_of_descent b f hind _ _ hdesc]
        · have hlen := (weylCoxeterSystem b).not_isRightDescent_iff.mp hdesc
          have hnotneg : (⟨n, hn⟩ : Fin word.length) ∉
              negativeSteps (weylCoxeterSystem b) expression := by
            intro h
            have hle : (weylCoxeterSystem b).BruhatLE
                (expression.prefixProd (weylCoxeterSystem b) (n + 1))
                (expression.prefixProd (weylCoxeterSystem b) n) := h.1
            rw [hs] at hle
            have h2 := hle.length_le
            rw [hlen] at h2
            omega
          have hnoteq : (⟨n, hn⟩ : Fin word.length) ∉
              equalSteps (weylCoxeterSystem b) expression := by
            intro h
            have h' : expression.prefixProd (weylCoxeterSystem b) n =
                expression.prefixProd (weylCoxeterSystem b) (n + 1) := h
            rw [hs] at h'
            have h2 := congrArg (weylCoxeterSystem b).length h'
            rw [hlen] at h2
            omega
          rw [hpos _ hnotneg hnoteq, hs, point_mul_simple b f hind _ _ hlen]
      · have heq0 : expression.prefixProd (weylCoxeterSystem b) n =
            expression.prefixProd (weylCoxeterSystem b) (n + 1) := by
          rw [hs, mul_one]
        rw [heq _ heq0, mul_one, heq0]
    · have hl1 : (List.ofFn step).length ≤ n + 1 := by
        rw [List.length_ofFn]
        omega
      have hl0 : (List.ofFn step).length ≤ n := by
        rw [List.length_ofFn]
        omega
      have hf1 : (expression.factors (weylCoxeterSystem b)).length ≤ n + 1 := by
        rw [Subexpression.length_factors]
        omega
      have hf0 : (expression.factors (weylCoxeterSystem b)).length ≤ n := by
        rw [Subexpression.length_factors]
        omega
      have h2 : expression.prefixProd (weylCoxeterSystem b) (n + 1) =
          expression.prefixProd (weylCoxeterSystem b) n := by
        rw [Subexpression.prefixProd, Subexpression.prefixProd, List.take_of_length_le hf1,
          List.take_of_length_le hf0]
      rw [List.take_of_length_le hl1, h2, ← ih, List.take_of_length_le hl0]

end Words

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The signed product of a subexpression prefix is the representative `u̇` of its Weyl element
`u`: the product of the simple representatives along a reduced word for `u`. -/
theorem subwordRepresentative_eq_weylElement {word : List G.rootBase.support}
    (expression : Subexpression word) (n : ℕ) :
    subwordRepresentative G expression n =
      weylElementPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹) G.rootBase
        (expression.prefixProd (weylCoxeterSystem G.rootBase) n) :=
  step_prod_eq G.rootBase (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹)
    G.invSimpleWordPoint_eq_of_reduced expression (subwordStepPoint G expression)
    (fun j hj => by
      unfold subwordStepPoint simpleRepresentative
      rw [ite_eq_left hj])
    (fun j hj => by
      unfold subwordStepPoint
      rw [ite_eq_right (fun h => h.2 (Eq.symm hj)), ite_eq_left hj])
    (fun j hn he => by
      unfold subwordStepPoint simpleRepresentative
      rw [ite_eq_right hn, ite_eq_right he])
    n

end
end SchubertGeometry
