import OrbitComplexity.ReductiveGroups.Groups.Reductive.CharacterRelations
import OrbitComplexity.ReductiveGroups.Lie.Roots.RootHeightLinearForm

/-! # Full-character relations preserve the integral root height -/

open ReductiveGroups TauCeti

noncomputable section
universe u

namespace ReductiveGroups.ReductiveGroupData

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- A relation in the full torus character group gives an integral height relation. -/
theorem rootCharacter_height (m : G.rootIndex →₀ ℤ)
    (hm : m.prod (fun r z => G.rootCharacter r ^ z) = 1) :
    m.sum (fun r z => z * G.rootBase.height r) = 0 := by
  have hr := (G.rootCharacter_relation m).mp hm
  have hK := congrArg (rootHeightLinearForm G.rootSystem G.rootBase) hr
  simp only [Finsupp.sum, map_sum, map_zsmul, rootHeightLinearForm_root, map_zero] at hK
  apply Int.cast_injective (α := K)
  simpa only [Finsupp.sum, Int.cast_sum, Int.cast_mul, Int.cast_zero, zsmul_eq_mul] using hK

end ReductiveGroups.ReductiveGroupData
