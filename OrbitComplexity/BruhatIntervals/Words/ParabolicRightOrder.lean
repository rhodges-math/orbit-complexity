import OrbitComplexity.BruhatIntervals.Words.ParabolicOrder
import OrbitComplexity.BruhatIntervals.Words.ParabolicDescents

/-! # Bruhat order on right parabolic cosets

Minimal right representatives inherit Bruhat comparison. A greatest parabolic element
provides the maximal member of each right coset, and its lower interval consists precisely
of the cosets whose minimal representatives lie below the given minimal representative.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Section 2.4.
-/

namespace BruhatIntervals
universe u v
variable {S : Type u} {W : Type v} [Group W] {M : CoxeterMatrix S}
  (cs : CoxeterSystem M W)

private theorem minimal_inv {J : Set S} {w : W} (hw : cs.IsMinimalCosetRep J w) :
    IsMinimalLeftRep cs J w⁻¹ := by
  intro a ha
  have h := hw a⁻¹ ((cs.parabolic J).inv_mem ha)
  have hi := cs.length_inv (w * a⁻¹)
  rw [mul_inv_rev, inv_inv] at hi
  rw [cs.length_inv, hi]
  exact h

/-- Bruhat comparison descends to the minimal right parabolic representatives. -/
theorem minimalRightRep_mono {J : Set S} {a b u v : W}
    (ha : a ∈ cs.parabolic J) (hb : b ∈ cs.parabolic J)
    (hu : cs.IsMinimalCosetRep J u) (hv : cs.IsMinimalCosetRep J v)
    (hle : cs.BruhatLE (u * a) (v * b)) : cs.BruhatLE u v := by
  have hinv := hle.inv
  simp only [mul_inv_rev] at hinv
  have h := minimalLeftRep_mono cs ((cs.parabolic J).inv_mem ha) (minimal_inv cs hu)
    ((cs.parabolic J).inv_mem hb) (minimal_inv cs hv) hinv
  simpa only [inv_inv] using h.inv

private theorem minimal_le_translate {J : Set S} {v a : W}
    (hv : cs.IsMinimalCosetRep J v) (ha : a ∈ cs.parabolic J) :
    cs.BruhatLE v (v * a) := by
  obtain ⟨first, hfirst, hfirstprod⟩ := cs.exists_isReduced v
  obtain ⟨last, hlast, hlastprod⟩ := cs.exists_isReduced a
  have hlength : cs.length (cs.wordProd first * cs.wordProd last) =
      cs.length (cs.wordProd first) + cs.length (cs.wordProd last) := by
    rw [← hfirstprod, ← hlastprod]
    exact cs.length_mul_of_isMinimalCosetRep hv ha
  have hred : cs.IsReduced (first ++ last) := by
    rw [CoxeterSystem.IsReduced, cs.wordProd_append, hlength, hfirst.eq, hlast.eq,
      List.length_append]
  have hbelow := cs.bruhatLE_wordProd_of_sublist hred (List.sublist_append_left first last)
  simpa only [cs.wordProd_append, ← hfirstprod, ← hlastprod] using hbelow

private theorem multiply_word_le {J : Set S} {top x : W}
    (hdescent : ∀ i ∈ J, cs.IsRightDescent top i) (hx : cs.BruhatLE x top)
    (word : List S) (hletters : ∀ i ∈ word, i ∈ J) :
    cs.BruhatLE (x * cs.wordProd word) top := by
  induction word generalizing x with
  | nil => simpa only [cs.wordProd_nil, mul_one] using hx
  | cons i word ih =>
    have hstep := hx.mul_simple_of_isRightDescent i (hdescent i (hletters i List.mem_cons_self))
    have htail := ih hstep (fun j hj => hletters j (List.mem_cons_of_mem i hj))
    simpa only [cs.wordProd_cons, ← mul_assoc] using htail

/-- A maximal parabolic suffix saturates the interval of its minimal representative. -/
theorem bruhatLE_parabolic_maximum_iff {J : Set S} {a b u v : W}
    (hb : b ∈ cs.parabolic J) (hu : cs.IsMinimalCosetRep J u)
    (hv : cs.IsMinimalCosetRep J v) :
    let : PartialOrder W := cs.bruhatPartialOrder
    IsGreatest (cs.parabolic J : Set W) a →
      (cs.BruhatLE (u * b) (v * a) ↔ cs.BruhatLE u v) := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro hmax
  constructor
  · exact minimalRightRep_mono cs hb hmax.1 hu hv
  · intro hle
    have hdescent (i : S) (hi : i ∈ J) : cs.IsRightDescent (v * a) i := by
      have has : a * cs.simple i ∈ cs.parabolic J :=
        (cs.parabolic J).mul_mem hmax.1 (cs.simple_mem_parabolic hi)
      have hbound : cs.BruhatLE (a * cs.simple i) a := hmax.2 has
      have hlen := hbound.length_le
      have hadd := cs.length_mul_of_isMinimalCosetRep hv hmax.1
      have hads := cs.length_mul_of_isMinimalCosetRep hv has
      by_contra hn
      have hinc := cs.not_isRightDescent_iff.mp hn
      rw [mul_assoc, hads, hadd] at hinc
      omega
    obtain ⟨word, hletters, hproduct⟩ := cs.exists_wordProd_eq_of_mem_parabolic hb
    rw [← hproduct]
    exact multiply_word_le cs hdescent (hle.trans (minimal_le_translate cs hv hmax.1))
      word hletters

end BruhatIntervals
