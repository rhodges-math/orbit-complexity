import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupInvolution
import TauCeti.Algebra.Lie.Weights.Chevalley.Twist
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Compatible root vectors in reductive tangent quotients -/

noncomputable section

namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule TauCeti

universe u v
variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

private theorem normalize_cartan_involution (ω : L ≃ₗ⁅K⁆ L)
    (hω : ∀ y ∈ H, ω y = -y) :
    ∃ x : Weight K H L → L, IsChevalleySystem ω x := by
  obtain ⟨x, hx⟩ := TauCeti.exists_isSl2System K H (L := L)
  have hnorm : H.map ω.toLieHom = H :=
    LieSubalgebra.map_eq_self_of_forall_mem_apply_eq_neg ω hω
  apply hx.exists_isChevalleySystem_of_forall_exists_sq ω hω
  intro α hα
  obtain ⟨c, _, hc⟩ := hx.exists_map_eq_smul ω hnorm hα
  have hc' : ω (x α) = c • x (-α) := by
    rwa [TauCeti.weightPerm_eq_neg ω hω] at hc
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (-c) (n := 2) (by decide)
  refine ⟨t, ?_⟩
  simpa only [ht, neg_neg] using hc'

namespace ReductiveGroupData

variable (G : ReductiveGroupData K)

/-- The center quotient has normalized root vectors compatible with a Lie involution. -/
theorem exists_chevalleySystem :
    ∃ (ω : G.centerQuotient ≃ₗ⁅K⁆ G.centerQuotient)
      (x : Weight K G.cartan G.centerQuotient → G.centerQuotient),
        IsChevalleySystem ω x := by
  obtain ⟨ω, hω, _⟩ := G.exists_cartanInvolution
  obtain ⟨x, hx⟩ := normalize_cartan_involution ω (fun y hy => hω ⟨y, hy⟩)
  exact ⟨ω, x, hx⟩

end ReductiveGroupData

end ReductiveGroups
