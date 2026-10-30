import OrbitComplexity.ReductiveGroups.Lie.Solvable.SolvableCartanCompatibleBase
import Mathlib.Algebra.Lie.Weights.Cartan

/-!
# Positive Root Height Bracket

Positive root-space brackets have the sum height. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule RootPairing

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (rootSystem H).Base)

private theorem positive_roots_sum_ne_zero
    (α β : H.root) (hα : b.IsPos α) (hβ : b.IsPos β) :
    ((α : H → K) + (β : H → K)) ≠ 0 := by
  intro hzero
  let P := rootSystem H
  have hroot : P.root β = -P.root α := by
    apply LinearMap.ext
    intro z
    have hz := congrFun hzero z
    simp only [Pi.add_apply, Pi.zero_apply] at hz
    change (β : H → K) z = -((α : H → K) z)
    exact eq_neg_of_add_eq_zero_right hz
  let := P.indexNeg
  have hβα : β = -α := P.root.injective (by simpa using hroot)
  have hh : b.height β = -b.height α := by
    rw [hβα]
    exact b.height_reflectionPerm_self α
  change 0 < b.height α at hα
  change 0 < b.height β at hβ
  omega

/-- Bracketing positive-root vectors either gives zero or lands in the
positive root space with exactly the sum of their heights. -/
theorem positive_root_bracket_mem_sum_height
    (α β : H.root) (hα : b.IsPos α) (hβ : b.IsPos β)
    (x y : L) (hx : x ∈ rootSpace H α.val) (hy : y ∈ rootSpace H β.val) :
    ⁅x, y⁆ ∈ ⨆ (γ : H.root) (_ : b.height γ = b.height α + b.height β),
      rootSpace H γ.val := by
  let χ : H → K := (α : H → K) + (β : H → K)
  have hxy : ⁅x, y⁆ ∈ rootSpace H χ :=
    lie_mem_genWeightSpace_of_mem_genWeightSpace hx hy
  by_cases hz : ⁅x, y⁆ = 0
  · rw [hz]
    exact zero_mem _
  have hnonbot : rootSpace H χ ≠ ⊥ := by
    intro hbot
    have : ⁅x, y⁆ = 0 := by
      simpa [hbot] using hxy
    exact hz this
  let γ : Weight K H L := ⟨χ, hnonbot⟩
  have hγ : γ.IsNonZero := positive_roots_sum_ne_zero H b α β hα hβ
  let γroot : H.root := ⟨γ, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hγ⟩⟩
  have hsum : (rootSystem H).root γroot =
      (rootSystem H).root α + (rootSystem H).root β := by
    rfl
  have hheight : b.height γroot = b.height α + b.height β := b.height_add hsum
  apply LieSubmodule.mem_iSup_of_mem γroot
  apply LieSubmodule.mem_iSup_of_mem hheight
  simpa [γroot, γ, χ] using hxy

end ReductiveGroups
