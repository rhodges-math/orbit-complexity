import OrbitComplexity.ReductiveGroups.Lie.Solvable.SolvableSl2Obstruction
import Mathlib.Algebra.Lie.Weights.Killing

/-!
# Solvable Root Subset

A solvable Lie subalgebra of a split Killing Lie algebra cannot contain
both root spaces for a nonzero root and its opposite. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- Both opposing nonzero root spaces cannot lie in a solvable Lie subalgebra.
The ambient Killing assumption is on `L`, not on the subalgebra. -/
theorem SolvableSubalgebra.not_contains_opposite_rootSpaces
    (S : LieSubalgebra K L) [LieAlgebra.IsSolvable S]
    (α : Weight K H L) (hα : α.IsNonZero)
    (hpos : ∀ x : L, x ∈ rootSpace H α → x ∈ S)
    (hneg : ∀ x : L, x ∈ rootSpace H (-α) → x ∈ S) : False := by
  obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have heS : e ∈ S := hpos e he
  have hfS : f ∈ S := hneg f hf
  have hhS : h ∈ S := ht.lie_e_f ▸ S.lie_mem heS hfS
  have htS : IsSl2Triple (⟨h, hhS⟩ : S) ⟨e, heS⟩ ⟨f, hfS⟩ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun hz => ht.h_ne_zero (congrArg Subtype.val hz)
    · apply Subtype.ext
      exact ht.lie_e_f
    · apply Subtype.ext
      exact ht.lie_h_e_nsmul
    · apply Subtype.ext
      exact ht.lie_h_f_nsmul
  exact not_isSolvable_of_sl2Triple (K := K) htS inferInstance

end ReductiveGroups
