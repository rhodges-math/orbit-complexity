import Batteries.Tactic.Lint
import OrbitComplexity.BruhatIntervals.Order.Covers
import Mathlib.Data.Nat.Init

/-!
# Directed cover paths inside Bruhat intervals

Every vertex of a Bruhat interval is reachable from its lower endpoint by intrinsic Bruhat
covers, with all vertices still in that interval. The partial order is introduced locally so
that a group is not assigned an order independently of its Coxeter system.
-/

namespace BruhatIntervals

variable {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

/-- Every interval vertex is reachable from the lower endpoint in the directed Bruhat cover
graph. The cover relation is the ambient Bruhat order restricted to interval vertices. -/
theorem bruhatInterval_cover_reachable (a b : W) (hab : cs.BruhatLE a b) :
    let : PartialOrder W := cs.bruhatPartialOrder
    ∀ x : bruhatInterval cs a b,
      Relation.ReflTransGen
        (fun p q : bruhatInterval cs a b => p.val ⋖ q.val)
        (⟨a, cs.bruhatLE_refl a, hab⟩ : bruhatInterval cs a b) x := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  let root : bruhatInterval cs a b := ⟨a, cs.bruhatLE_refl a, hab⟩
  suffices aux : ∀ n : ℕ, ∀ x : bruhatInterval cs a b, cs.length x.val = n →
      Relation.ReflTransGen
        (fun p q : bruhatInterval cs a b => p.val ⋖ q.val) root x by
    intro x
    exact aux (cs.length x.val) x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x hxlength
      by_cases heq : a = x.val
      · have hx : x = root := Subtype.ext heq.symm
        rw [hx]
      obtain ⟨z, haz, hzx⟩ := exists_le_bruhat_covBy cs x.property.1 heq
      have hzle : cs.BruhatLE z x.val := hzx.le
      let z' : bruhatInterval cs a b := ⟨z, haz, hzle.trans x.property.2⟩
      have hzlength : cs.length z < n := by
        rw [← hxlength]
        exact hzle.length_lt_of_ne hzx.ne
      have hpath := ih (cs.length z) hzlength z' rfl
      exact hpath.tail hzx

end BruhatIntervals
