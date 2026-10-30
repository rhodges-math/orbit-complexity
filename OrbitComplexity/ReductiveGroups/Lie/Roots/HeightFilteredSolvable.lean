import Mathlib.Algebra.Lie.Solvable

/-!
# Height Filtered Solvable

A finite positive-degree filtration with strictly rising brackets
terminates the derived series. -/

namespace ReductiveGroups

variable {K B : Type*} [CommRing K] [LieRing B] [LieAlgebra K B]

/-- A derived series controlled by a bracket-raising filtration terminates
as soon as the filtration does. -/
theorem HeightFilteredSolvable.isSolvable_bracket_raising_filtration
    (F : ℕ → LieIdeal K B)
    (hfirst : LieAlgebra.derivedSeries K B 1 ≤ F 0)
    (hraise : ∀ n, ⁅F n, F n⁆ ≤ F (n + 1))
    (N : ℕ) (hterminal : F N = ⊥) : LieAlgebra.IsSolvable B := by
  have hderived (n : ℕ) : LieAlgebra.derivedSeries K B (n + 1) ≤ F n := by
    induction n with
    | zero => simpa using hfirst
    | succ n ih =>
        rw [LieAlgebra.derivedSeries_def,
          LieAlgebra.derivedSeriesOfIdeal_succ]
        exact (LieSubmodule.mono_lie ih ih).trans (hraise n)
  apply LieAlgebra.IsSolvable.mk (R := K)
  exact eq_bot_iff.mpr ((hderived N).trans (by rw [hterminal]))

end ReductiveGroups
