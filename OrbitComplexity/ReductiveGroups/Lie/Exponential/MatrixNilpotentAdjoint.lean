import Mathlib.Algebra.Lie.AdjointAction.Basic

/-!
# Matrix Nilpotent Adjoint

Faithful matrix Lie representations detect nilpotence of the adjoint. -/

noncomputable section
namespace ReductiveGroups

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- Associative nilpotence in any faithful associative Lie representation
forces nilpotence of the original adjoint action. -/
theorem MatrixNilpotentAdjoint.ad_injective_associative_representation
    {A : Type*} [Ring A] [Algebra K A]
    (f : L →ₗ⁅K⁆ A) (hf : Function.Injective f) (x : L)
    (hx : IsNilpotent (f x)) :
    IsNilpotent (LieAlgebra.ad K L x) := by
  have hA : IsNilpotent (LieAlgebra.ad K A (f x)) :=
    LieAlgebra.ad_nilpotent_of_nilpotent hx
  obtain ⟨r, hr⟩ := hA
  refine ⟨r, ?_⟩
  apply LinearMap.ext
  intro y
  apply hf
  have hpow (k : ℕ) (z : L) :
      f (((LieAlgebra.ad K L x) ^ k) z) =
        ((LieAlgebra.ad K A (f x)) ^ k) (f z) := by
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          f (((LieAlgebra.ad K L x) ^ (k + 1)) z) =
              f ⁅x, ((LieAlgebra.ad K L x) ^ k) z⁆ := by
                rw [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
          _ = ⁅f x, f (((LieAlgebra.ad K L x) ^ k) z)⁆ := f.map_lie x _
          _ = ⁅f x, ((LieAlgebra.ad K A (f x)) ^ k) (f z)⁆ := by rw [ih]
          _ = ((LieAlgebra.ad K A (f x)) ^ (k + 1)) (f z) := by
            rw [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
  have h := hpow r y
  rw [hr] at h
  simpa using h

end ReductiveGroups
