import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralRadicalQuotient

/-! # Automorphisms on the center quotient of a Lie algebra -/

noncomputable section
namespace ReductiveGroups
universe u v
variable {K : Type u} [Field K] {L : Type v} [LieRing L] [LieAlgebra K L]

private theorem center_map (e : L ≃ₗ⁅K⁆ L) :
    (LieAlgebra.center K L).toSubmodule.map e.toLinearEquiv.toLinearMap =
      (LieAlgebra.center K L).toSubmodule := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply (LieModule.mem_maxTrivSubmodule K L L (e y)).mpr
    intro z
    obtain ⟨a, rfl⟩ := e.surjective z
    change ⁅e a, e y⁆ = 0
    rw [← e.map_lie]
    rw [(LieModule.mem_maxTrivSubmodule K L L y).mp hy a, map_zero]
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply (LieModule.mem_maxTrivSubmodule K L L (e.symm x)).mpr
    intro z
    apply e.injective
    change e ⁅z, e.symm x⁆ = e (0 : L)
    rw [map_zero, e.map_lie, e.apply_symm_apply]
    exact (LieModule.mem_maxTrivSubmodule K L L x).mp hx (e z)

/-- A Lie automorphism induces a Lie automorphism after quotienting by the center. -/
def centerQuotientEquiv (e : L ≃ₗ⁅K⁆ L) :
    (L ⧸ LieAlgebra.center K L) ≃ₗ⁅K⁆ (L ⧸ LieAlgebra.center K L) where
  __ := Submodule.Quotient.equiv (LieAlgebra.center K L).toSubmodule
    (LieAlgebra.center K L).toSubmodule e.toLinearEquiv (center_map e)
  map_lie' := by
    intro x y
    induction x, y using Quotient.inductionOn₂' with
    | _ a b =>
      change Submodule.Quotient.mk (e ⁅a, b⁆) = Submodule.Quotient.mk ⁅e a, e b⁆
      rw [e.map_lie]

/-- The induced automorphism commutes with the center quotient map. -/
theorem centerQuotientEquiv_apply (e : L ≃ₗ⁅K⁆ L) (x : L) :
    centerQuotientEquiv e (centerQuotientLieHom (K := K) x) =
      centerQuotientLieHom (K := K) (e x) := rfl

end ReductiveGroups
