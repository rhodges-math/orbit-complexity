import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Algebra.Lie.Solvable

/-!
# Central Root Derived

Nonzero root spaces of a Lie algebra lie in its derived ideal. -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra LieModule

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  (H : LieSubalgebra K L) [LieRing.IsNilpotent H]

/-- A generalized eigenvector for a nonzero weight is in the derived ideal:
every adjoint action lands there, so the nonzero scalar part can be solved for. -/
theorem rootSpace_le_derivedSeries_one (χ : H → K) (hχ : χ ≠ 0) :
    rootSpace H χ ≤ (derivedSeries K L 1).restr H := by
  obtain ⟨h, hh⟩ : ∃ h : H, χ h ≠ 0 := by
    by_contra hn
    apply hχ
    funext h
    simpa using (not_exists.mp hn h)
  let D := derivedSeries K L 1
  have hbr (u v : L) : ⁅u, v⁆ ∈ D := by
    change ⁅u, v⁆ ∈ D.toLieSubalgebra.toSubmodule
    rw [LieAlgebra.coe_derivedSeries_one_eq K L]
    exact Submodule.subset_span ⟨u, v, rfl⟩
  have haux (k : ℕ) : ∀ x : L,
      (((toEnd K H L) h - χ h • (1 : Module.End K L)) ^ k) x = 0 → x ∈ D := by
    induction k with
    | zero =>
        intro x hx
        have : x = 0 := by simpa using hx
        rw [this]
        exact D.zero_mem
    | succ k ih =>
        intro x hx
        have hy : (((toEnd K H L) h - χ h • (1 : Module.End K L)) ^ k)
            (((toEnd K H L) h - χ h • (1 : Module.End K L)) x) = 0 := by
          simpa only [pow_succ, Module.End.mul_apply] using hx
        have hY := ih _ hy
        have hs : χ h • x ∈ D := by
          have heq : ((toEnd K H L) h - χ h • (1 : Module.End K L)) x =
              ⁅(h : L), x⁆ - χ h • x := by simp [LieModule.toEnd_apply_apply]
          rw [heq] at hY
          have hB := hbr (h : L) x
          have : χ h • x = ⁅(h : L), x⁆ - (⁅(h : L), x⁆ - χ h • x) := by abel
          rw [this]
          exact D.sub_mem hB hY
        exact (D.toLieSubalgebra.toSubmodule.smul_mem_iff hh).mp hs
  intro x hx
  obtain ⟨k, hk⟩ := (mem_genWeightSpace L χ x).mp hx h
  exact haux k x hk

/-- A weight occurring in the adjoint representation is zero on every
central element of the acting subalgebra. -/
theorem rootWeight_apply_eq_zero_of_mem_center
    (α : Weight K H L) (h : H) (hh : (h : L) ∈ center K L) :
    α h = 0 := by
  obtain ⟨x, hx, hx0⟩ := α.exists_ne_zero
  have hz : (toEnd K H L) h = 0 := by
    ext y
    have hc : ⁅y, (h : L)⁆ = 0 :=
      (mem_maxTrivSubmodule K L L (h : L)).mp hh y
    change ⁅(h : L), y⁆ = 0
    calc
      ⁅(h : L), y⁆ = -⁅y, (h : L)⁆ := (lie_skew (h : L) y).symm
      _ = 0 := by rw [hc, neg_zero]
  obtain ⟨k, hk⟩ := (mem_genWeightSpace L (α : H → K) x).mp hx h
  rw [hz] at hk
  have hscalar : (-α h) ^ k • x = 0 := by
    rw [zero_sub, ← neg_smul, smul_pow, one_pow] at hk
    simpa using hk
  by_contra ha
  have hp : (-α h) ^ k ≠ 0 := pow_ne_zero k (neg_ne_zero.mpr ha)
  exact hx0 ((smul_eq_zero.mp hscalar).resolve_left hp)

end ReductiveGroups
