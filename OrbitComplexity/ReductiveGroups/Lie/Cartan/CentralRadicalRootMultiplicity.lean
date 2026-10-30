import OrbitComplexity.ReductiveGroups.Lie.Cartan.CenterQuotientWeightDescent
import Mathlib.Algebra.Lie.Weights.Killing

/-!
# Central Radical Root Multiplicity

Nonzero roots of a reductive Lie algebra have one-dimensional root
spaces. Killing nondegeneracy is used only on the center quotient. -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra LieModule

variable {K L : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [LieAlgebra.HasCentralRadical K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

/-- The center quotient preserves nonzero root spaces, so its
one-dimensional-root theorem applies without discarding the original center. -/
theorem centralRadical_finrank_rootSpace_eq_one
    (χ : Weight K H L) (hχ : χ.IsNonZero) :
    Module.finrank K (rootSpace H χ) = 1 := by
  let _ := centralRadical_centerQuotient_isKilling (K := K) (L := L)
  have hker : ((centerQuotientLieHom (K := K) (L := L)).ker : LieSubalgebra K L) ≤ H := by
    rw [centerQuotientLieHom_ker]
    exact center_le_cartan H
  let _ := cartan_map_of_surjective (centerQuotientLieHom (K := K))
    centerQuotientLieHom_surjective H hker
  let ψ := centerQuotientWeightOfNonZero H χ hχ
  have hψ : ψ.IsNonZero := by
    intro hz
    apply centerQuotientWeightDescent_ne_zero H χ hχ
    exact DFunLike.coe_injective hz
  have heval : (fun h : H => ψ (centerQuotientCartanMap H h)) = (χ : H → K) := by
    funext h
    exact centerQuotientWeightDescent_apply_map H χ h
  have hrank := (centerQuotientRootSpaceEquiv H (ψ : centerQuotientCartan H → K) hψ).finrank_eq
  rw [heval] at hrank
  exact hrank.trans (LieAlgebra.IsKilling.finrank_rootSpace_eq_one ψ hψ)

end ReductiveGroups
