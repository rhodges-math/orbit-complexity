import OrbitComplexity.BruhatIntervals.Graph.ThinIntervals
import Mathlib.Data.Set.Card

/-! # Cardinality of rank-two Bruhat intervals

Cover grading and the two-cover diamond theorem enumerate the four interval elements.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Lemma 2.7.3.
-/

namespace BruhatIntervals
variable {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

/-- A comparable Bruhat interval with Coxeter length difference two has four elements. -/
theorem bruhatInterval_ncard_of_rank_two (u v : W) (hle : cs.BruhatLE u v)
    (hgap : cs.length v - cs.length u = 2) : (bruhatInterval cs u v).ncard = 4 := by
  let : PartialOrder W := cs.bruhatPartialOrder
  have hlen : cs.length v = cs.length u + 2 := by omega
  have huv : u ≠ v := by
    intro he
    rw [he] at hlen
    omega
  obtain ⟨x, hux, hxv⟩ := exists_bruhat_covBy_le cs hle huv
  have hxl := ((bruhat_covBy_iff cs u x).mp hux).2
  have hxv' : x ⋖ v := (bruhat_covBy_iff cs x v).mpr ⟨hxv, by omega⟩
  obtain ⟨y, ⟨hyx, huy, hyv⟩, hunique⟩ := bruhat_rank_two_diamond cs u x v hux hxv'
  apply Set.ncard_eq_four.mpr
  refine ⟨u, x, y, v, hux.lt.ne, huy.lt.ne, huv, hyx.symm, hxv'.lt.ne, hyv.lt.ne, ?_⟩
  ext w
  change (cs.BruhatLE u w ∧ cs.BruhatLE w v) ↔ w = u ∨ w = x ∨ w = y ∨ w = v
  constructor
  · intro hw
    by_cases hwu : w = u
    · exact Or.inl hwu
    by_cases hwv : w = v
    · exact Or.inr (Or.inr (Or.inr hwv))
    by_cases hwx : w = x
    · exact Or.inr (Or.inl hwx)
    have hlow := hw.1.length_lt_of_ne (fun he => hwu he.symm)
    have hhigh := hw.2.length_lt_of_ne hwv
    have hmiddle : cs.length w = cs.length u + 1 := by omega
    have huw : u ⋖ w := (bruhat_covBy_iff cs u w).mpr ⟨hw.1, hmiddle⟩
    have hwv' : w ⋖ v := (bruhat_covBy_iff cs w v).mpr ⟨hw.2, by omega⟩
    exact Or.inr (Or.inr (Or.inl (hunique w ⟨hwx, huw, hwv'⟩)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨cs.bruhatLE_refl _, hle⟩
    · exact ⟨hux.le, hxv⟩
    · exact ⟨huy.le, hyv.le⟩
    · exact ⟨hle, cs.bruhatLE_refl _⟩

end BruhatIntervals
