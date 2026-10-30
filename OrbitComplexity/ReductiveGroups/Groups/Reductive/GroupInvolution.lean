import OrbitComplexity.ReductiveGroups.Lie.Basis.Involution
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootData
import Mathlib.Algebra.Lie.Basis.Base

/-! # Cartan-inverting involutions for reductive tangent quotients -/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The tangent algebra modulo its center has an involution inverting the chosen Cartan. -/
theorem exists_cartanInvolution :
    ∃ ω : G.centerQuotient ≃ₗ⁅K⁆ G.centerQuotient,
      (∀ h : G.cartan, ω (h : G.centerQuotient) = -(h : G.centerQuotient)) ∧
        Function.Involutive ω := by
  obtain ⟨b, _, _⟩ := LieAlgebra.exists_basis_of_base G.rootBase
  obtain ⟨ω, hω, _, hωω⟩ := ReductiveGroups.LieBasis.exists_cartan_involution b
  exact ⟨ω, hω, hωω⟩

end ReductiveGroups.ReductiveGroupData
