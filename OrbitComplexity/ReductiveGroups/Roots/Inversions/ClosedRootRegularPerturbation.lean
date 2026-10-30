import OrbitComplexity.ReductiveGroups.Roots.Inversions.ClosedRootFunctionalBase

/-!
# Closed Root Regular Perturbation

A rational functional positive on finitely many roots can be made regular
without losing any required positive signs. -/

noncomputable section
namespace ReductiveGroups

open RootPairing

universe u v w₁ w₂
variable {ι : Type u} {R : Type v} {M : Type w₁} {N : Type w₂}
  [Finite ι] [AddCommGroup M] [AddCommGroup N]
  [Field R] [CharZero R] [Module R M] [Module R N]
  (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]

omit [P.IsRootSystem] [P.IsCrystallographic] in
/-- Positivity on a finite root subset can be kept while avoiding all root
hyperplanes. -/
theorem exists_regular_positive_root_form
    (s : Set ι) (f : M →+ ℚ) (hf : ∀ i ∈ s, 0 < f (P.root i)) :
    ∃ g : M →+ ℚ, (∀ i, g (P.root i) ≠ 0) ∧
      ∀ i ∈ s, 0 < g (P.root i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℚ M, ∀ i, g (P.root i) ≠ 0 :=
    Module.exists_dual_forall_apply_ne_zero P.root (by simp [P.ne_zero])
  let q (i : ι) : ℚ := |g (P.root i)| / |f (P.root i)|
  let B : ℚ := ∑ i, q i
  have hqnon (i : ι) : 0 ≤ q i := div_nonneg (abs_nonneg _) (abs_nonneg _)
  have hqle (i : ι) : q i ≤ B :=
    Finset.single_le_sum (fun j _ => hqnon j) (Finset.mem_univ i)
  obtain ⟨n, hn⟩ := exists_nat_gt B
  have hdom (i : ι) (hfi : f (P.root i) ≠ 0) :
      |g (P.root i)| < (n : ℚ) * |f (P.root i)| := by
    have h : q i < (n : ℚ) := lt_of_le_of_lt (hqle i) hn
    exact (div_lt_iff₀ (abs_pos.mpr hfi)).mp h
  let g' : M →+ ℚ := n • f + g.toAddMonoidHom
  refine ⟨g', ?_, ?_⟩
  · intro i
    by_cases hfi : f (P.root i) = 0
    · simpa [g', hfi] using hg i
    · intro hz
      have habs : |g (P.root i)| = (n : ℚ) * |f (P.root i)| := by
        have heq : g (P.root i) = -((n : ℚ) * f (P.root i)) := by
          have hz' : (n : ℚ) * f (P.root i) + g (P.root i) = 0 := by
            simpa [g', nsmul_eq_mul] using hz
          linear_combination hz'
        rw [heq, abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      exact (ne_of_lt (hdom i hfi)) habs
  · intro i hi
    have hfi := hf i hi
    have hgf : |g (P.root i)| < (n : ℚ) * f (P.root i) := by
      simpa [abs_of_pos hfi] using hdom i (ne_of_gt hfi)
    have := neg_abs_le (g (P.root i))
    have hpos : 0 < (n : ℚ) * f (P.root i) + g (P.root i) := by linarith
    simpa [g', nsmul_eq_mul] using hpos

end ReductiveGroups
