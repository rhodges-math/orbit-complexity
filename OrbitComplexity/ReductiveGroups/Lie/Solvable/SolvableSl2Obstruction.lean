import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Solvable

/-!
# Solvable Sl 2 Obstruction

A solvable Lie algebra cannot contain an sl2 triple. This is
the obstruction needed to exclude opposing root spaces in a Borel tangent. -/

noncomputable section
namespace ReductiveGroups

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]

/-- Each member of an sl2 triple belongs to every derived-series term. -/
theorem sl2Triple_mem_derivedSeries {h e f : L} (ht : IsSl2Triple h e f) (n : ℕ) :
    h ∈ LieAlgebra.derivedSeries K L n ∧
    e ∈ LieAlgebra.derivedSeries K L n ∧
    f ∈ LieAlgebra.derivedSeries K L n := by
  induction n with
  | zero => exact ⟨LieSubmodule.mem_top _, LieSubmodule.mem_top _, LieSubmodule.mem_top _⟩
  | succ n ih =>
      have hb (x y : L) (hx : x ∈ LieAlgebra.derivedSeries K L n)
          (hy : y ∈ LieAlgebra.derivedSeries K L n) :
          ⁅x, y⁆ ∈ LieAlgebra.derivedSeries K L (n + 1) := by
        simpa only [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ] using
          LieSubmodule.lie_mem_lie hx hy
      have hef := hb e f ih.2.1 ih.2.2
      have hhe := hb h e ih.1 ih.2.1
      have hhf := hb h f ih.1 ih.2.2
      refine ⟨?_, ?_, ?_⟩
      · simpa only [ht.lie_e_f] using hef
      · rw [ht.lie_h_e_smul K] at hhe
        have hz := (LieAlgebra.derivedSeries K L (n + 1)).smul_mem (2 : K)⁻¹ hhe
        simpa only [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : K) ≠ 0),
          one_smul, LieSubmodule.mem_toSubmodule] using hz
      · rw [ht.lie_lie_smul_f K] at hhf
        have hneg := (LieAlgebra.derivedSeries K L (n + 1)).neg_mem hhf
        rw [neg_neg] at hneg
        have hz := (LieAlgebra.derivedSeries K L (n + 1)).smul_mem (2 : K)⁻¹ hneg
        simpa only [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : K) ≠ 0),
          one_smul, LieSubmodule.mem_toSubmodule] using hz

include K in
/-- Nonzero sl2 triples obstruct solvability, in arbitrary dimension. -/
theorem not_isSolvable_of_sl2Triple {h e f : L} (ht : IsSl2Triple h e f) :
    ¬ LieAlgebra.IsSolvable L := by
  intro hs
  let _ := hs
  obtain ⟨n, hn⟩ := LieAlgebra.IsSolvable.solvable K L
  have hm := (sl2Triple_mem_derivedSeries (K := K) ht n).1
  rw [hn, LieSubmodule.mem_bot] at hm
  exact ht.h_ne_zero hm

end ReductiveGroups
