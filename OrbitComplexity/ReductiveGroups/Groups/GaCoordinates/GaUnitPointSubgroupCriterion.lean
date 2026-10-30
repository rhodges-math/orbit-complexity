import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaUnitPointDeterminesMorphism
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# Ga Unit Point Subgroup Criterion

An additive one-parameter subgroup factors through a closed
subgroup exactly when its point at parameter `1` belongs to that subgroup. -/

noncomputable section
namespace ReductiveGroups

variable {K B : Type*} [Field K] [CharZero K] [CommRing B] [HopfAlgebra K B]

private theorem gaAffineGroupPoints_natCast_eq_pow
    (x : B →ₐc[K] SymmetricAlgebra K K) (n : ℕ) :
    gaAffineGroupPoints x (Multiplicative.ofAdd (n : K)) =
      (gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K))) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn : Multiplicative.ofAdd ((n + 1 : ℕ) : K) =
          Multiplicative.ofAdd (n : K) * Multiplicative.ofAdd (1 : K) := by
        simp [Nat.cast_add]
      rw [hn, map_mul, ih, pow_succ]

/-- Membership of the point at parameter `1` in a closed subgroup
forces its entire coordinate Ga morphism to annihilate the subgroup ideal. -/
theorem GaMorphism.kills_hopfIdeal_iff_unitPoint_mem
    (x : B →ₐc[K] SymmetricAlgebra K K) (I : TauCeti.HopfIdeal K B) :
    (∀ b ∈ I, x b = 0) ↔
      gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup
          (CommHopfAlgCat.of K B) I (CommAlgCat.of K K) := by
  constructor
  · intro h
    apply (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff
      (CommHopfAlgCat.of K B) I (CommAlgCat.of K K) _).mpr
    intro b hb
    change ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
      (Multiplicative.ofAdd (1 : K))).ofConv (x b) = 0
    rw [h b hb, map_zero]
  · intro h b hb
    apply (gaPolynomialEquiv K).injective
    apply Polynomial.eq_of_infinite_eval_eq
    have hinf : Set.Infinite (Set.range (fun n : ℕ => (n : K))) :=
      Set.infinite_range_of_injective Nat.cast_injective
    apply hinf.mono
    rintro t ⟨n, rfl⟩
    change Polynomial.eval (n : K) ((gaPolynomialEquiv K) (x b)) =
      Polynomial.eval (n : K) ((gaPolynomialEquiv K) 0)
    rw [gaPolynomialEquiv_eval_point, map_zero, Polynomial.eval_zero]
    have hn : gaAffineGroupPoints x (Multiplicative.ofAdd (n : K)) ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup
          (CommHopfAlgCat.of K B) I (CommAlgCat.of K K) := by
      rw [gaAffineGroupPoints_natCast_eq_pow]
      exact pow_mem h n
    exact (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff
      (CommHopfAlgCat.of K B) I (CommAlgCat.of K K) _).mp hn b hb

end ReductiveGroups
