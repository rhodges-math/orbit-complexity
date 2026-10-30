import OrbitComplexity.ReductiveGroups.Lie.Roots.RootStringNonvanishing

/-!
# Root Space Subalgebra Closure

Whole root spaces contained in a Lie subalgebra are closed under
addition whenever the sum is a nonzero root. -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra LieAlgebra.IsKilling LieModule

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  [IsTriangularizable K H L]

/-- Bracket nonvanishing and one-dimensionality force the full root space
of a nonzero sum into any subalgebra containing the two input root spaces. -/
theorem subalgebra_contains_rootSpace_of_sum
    (S : LieSubalgebra K L) (α β γ : Weight K H L)
    (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
    (hsum : (γ : H → K) = α + β)
    (hSα : ∀ x, x ∈ rootSpace H α → x ∈ S)
    (hSβ : ∀ x, x ∈ rootSpace H β → x ∈ S) :
    ∀ z, z ∈ rootSpace H γ → z ∈ S := by
  obtain ⟨x, hx, hx0⟩ := α.exists_ne_zero
  obtain ⟨y, hy, hy0⟩ := β.exists_ne_zero
  have hxy0 := rootSpace_lie_ne_zero_of_sum_root α β γ hα hβ hγ hsum x y hx hy hx0 hy0
  have hxy : ⁅x, y⁆ ∈ rootSpace H γ := by
    rw [hsum]
    exact lie_mem_genWeightSpace_of_mem_genWeightSpace hx hy
  intro z hz
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    (⟨⁅x, y⁆, hxy⟩ : rootSpace H γ) (by
      simpa only [ne_eq, LieSubmodule.mk_eq_zero] using hxy0)).mp
        (finrank_rootSpace_eq_one γ hγ) ⟨z, hz⟩
  have heq : c • ⁅x, y⁆ = z := congrArg Subtype.val hc
  rw [← heq]
  exact S.smul_mem c (S.lie_mem (hSα x hx) (hSβ y hy))

end ReductiveGroups
