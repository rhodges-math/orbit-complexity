import OrbitComplexity.BruhatIntervals.Graph.ThinIntervals
import Batteries.Tactic.Lint

/-! # Two covers in a Bruhat interval

Every interval of rank at least two has two distinct covers immediately
below its top. That top is a minimal common upper bound of those covers.
-/

set_option autoImplicit false

open CoxeterSystem

namespace BruhatIntervals

variable {S W : Type*} [Group W] {M : CoxeterMatrix S}
    (cs : CoxeterSystem M W)

/-- An interval of rank at least two contains two distinct covers immediately
below its top, each above its bottom. -/
theorem exists_two_bruhat_covBy (u v : W) (hle : cs.BruhatLE u v)
    (hlen : cs.length u + 2 ≤ cs.length v) :
    let : PartialOrder W := cs.bruhatPartialOrder
    ∃ a b : W, a ≠ b ∧ a ⋖ v ∧ b ⋖ v ∧ cs.BruhatLE u a ∧ cs.BruhatLE u b := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  have huv : u ≠ v := by
    intro h
    have heq := congrArg cs.length h
    omega
  obtain ⟨a, hua, hav⟩ := exists_le_bruhat_covBy cs hle huv
  have hla := (bruhat_covBy_iff cs a v).mp hav
  have hua' : u ≠ a := by
    intro h
    have heq := congrArg cs.length h
    omega
  obtain ⟨z, huz, hza⟩ := exists_le_bruhat_covBy cs hua hua'
  obtain ⟨b, hb, _⟩ := bruhat_rank_two_diamond cs z a v hza hav
  rcases hb with ⟨hba, hzb, hbv⟩
  exact ⟨a, b, hba.symm, hav, hbv, hua,
    huz.trans (show cs.BruhatLE z b from hzb.le)⟩

/-- The common top of two distinct lower covers is a minimal common upper
bound of those covers. -/
theorem bruhat_cover_minimal_upper (a b w z : W) (hab : a ≠ b) :
    let : PartialOrder W := cs.bruhatPartialOrder
    a ⋖ w → b ⋖ w → cs.BruhatLE a z → cs.BruhatLE b z →
      cs.BruhatLE z w → z = w := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro ha hb haz hbz hzw
  rcases ha.eq_or_eq haz hzw with hza | hzw'
  · subst z
    rcases hb.eq_or_eq hbz ha.le with hab' | haw
    · exact (hab hab').elim
    · exact (ha.ne haw).elim
  · exact hzw'

end BruhatIntervals
