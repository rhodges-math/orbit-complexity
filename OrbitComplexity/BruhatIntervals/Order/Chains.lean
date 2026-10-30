import OrbitComplexity.BruhatIntervals.Order.Covers
import Mathlib.Data.List.Chain

/-!
# Saturated endpoint chains in Bruhat order

Every interval admits a nonempty list joining its endpoints by covers. The list has one more
vertex than the Coxeter-length difference of the endpoints.

## Main results

* `exists_bruhat_chain`: a saturated endpoint list exists and has the expected length.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.2.
-/

namespace BruhatIntervals

variable {Index W : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

/-- A Bruhat interval has a saturated endpoint list with one more vertex than its length gap. -/
theorem exists_bruhat_chain (u v : W) (huv : cs.BruhatLE u v) :
    ∃ vertices : List W, vertices.head? = some u ∧ vertices.getLast? = some v ∧
      vertices.IsChain (fun x y => cs.BruhatLE x y ∧ cs.length y = cs.length x + 1) ∧
      vertices.length = cs.length v - cs.length u + 1 := by
  let : PartialOrder W := cs.bruhatPartialOrder
  suffices aux : ∀ n : ℕ, ∀ u v : W, cs.length v - cs.length u = n →
      cs.BruhatLE u v →
      ∃ vertices : List W, vertices.head? = some u ∧ vertices.getLast? = some v ∧
        vertices.IsChain (fun x y => cs.BruhatLE x y ∧ cs.length y = cs.length x + 1) ∧
        vertices.length = cs.length v - cs.length u + 1 by
    exact aux (cs.length v - cs.length u) u v rfl huv
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u v hgap huv
    by_cases heq : u = v
    · subst v
      exact ⟨[u], rfl, rfl, List.isChain_singleton u, by simp⟩
    obtain ⟨z, hcov, hzv⟩ := exists_bruhat_covBy_le cs huv heq
    have hzlength := ((bruhat_covBy_iff cs u z).mp hcov).2
    obtain ⟨vertices, hhead, hlast, hchain, hlength⟩ :=
      ih (cs.length v - cs.length z) (by have := hzv.length_le; omega) z v rfl hzv
    cases vertices with
    | nil => simp at hhead
    | cons first rest =>
      have hfirst : first = z := Option.some.inj hhead
      subst first
      refine ⟨u :: z :: rest, rfl, ?_, ?_, ?_⟩
      · simpa only [List.getLast?_cons_cons] using hlast
      · exact List.isChain_cons_cons.mpr ⟨⟨hcov.le, hzlength⟩, hchain⟩
      · simp only [List.length_cons] at hlength ⊢
        have := hzv.length_le
        omega

end BruhatIntervals

