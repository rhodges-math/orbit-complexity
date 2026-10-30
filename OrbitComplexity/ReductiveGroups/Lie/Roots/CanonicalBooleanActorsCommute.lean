import OrbitComplexity.ReductiveGroups.Lie.Roots.CanonicalRootWeightRealization
import OrbitComplexity.ReductiveGroups.Roots.Supports.DoubleBondMixedAtomicPartition
import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootSums

/-!
# Canonical Boolean Actors Commute

Root vectors at Boolean inversion roots commute. This is a
Lie bracket statement, not merely a statement about root-vector sums. -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra LieAlgebra.IsKilling LieModule

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
  [IsTriangularizable K H L]

/-- The equality is

```lean
⁅x, y⁆ = 0
```
-/
theorem canonical_boolean_root_vectors_commute
    (b : (rootSystem H).Base) (word : List b.support) (hword : word.Nodup)
    (α β : H.root)
    (hα : α ∈ leftRootInversionIndices b (simpleWeylWord b word))
    (hβ : β ∈ leftRootInversionIndices b (simpleWeylWord b word))
    (x y : L) (hx : x ∈ rootSpace H (α : Weight K H L))
    (hy : y ∈ rootSpace H (β : Weight K H L)) : ⁅x, y⁆ = 0 := by
  let f : Module.Dual K H := (rootSystem H).root α + (rootSystem H).root β
  have hf : f ≠ 0 := by
    have hpos : ∀ γ ∈ [α, β], b.IsPos γ := by
      intro γ hγ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl
      · exact hα.1
      · exact hβ.1
    simpa [f] using root_sum_ne_zero_of_positive b [α, β] (by simp) hpos
  have hbot : genWeightSpace L (f : H → K) = ⊥ := by
    by_contra hne
    let χ : Weight K H L := ⟨(f : H → K), hne⟩
    have hχ : χ.IsNonZero := by
      apply Weight.coe_toLinear_ne_zero_iff.mp
      intro hz
      apply hf
      ext h
      exact congrArg (fun g : Module.Dual K H => g h) hz
    let δ : H.root := ⟨χ, by simpa [LieSubalgebra.root] using hχ⟩
    have hsum : (rootSystem H).root δ =
        (rootSystem H).root α + (rootSystem H).root β := by
      ext h
      rfl
    exact boolean_inversion_pair_not_root b word hword hα hβ hsum
  have hmem := lie_mem_genWeightSpace_of_mem_genWeightSpace hx hy
  change ⁅x, y⁆ ∈ genWeightSpace L (f : H → K) at hmem
  rw [hbot] at hmem
  simpa only [LieSubmodule.mem_bot] using hmem

end ReductiveGroups
