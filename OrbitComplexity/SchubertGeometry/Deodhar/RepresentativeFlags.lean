import OrbitComplexity.SchubertGeometry.Cells.CellChart
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBruhatSystem

/-! # Flags of simple representative products

The inverse of a simple reflection point has the same Borel flag as the corresponding
Weyl extension. Left multiplication gives the corresponding root-product flag formula.
-/

open ReductiveGroups
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem inverseSimpleProduct (w : G.weylGroup) (i : G.rootBase.support) :
    ∃ t ∈ G.torusPoints, G.weylPoint w * (G.reflectionPoint i.val)⁻¹ =
      t * G.weylPoint (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  obtain ⟨t₀, ht₀, h₀⟩ := (G.isBruhatSystem.rankOne i).inv_eq
  obtain ⟨t₁, ht₁, h₁⟩ := G.isBruhatSystem.weyl.simple_eq_mul_weylElementPoint G.rootBase i
  have h₁' : G.reflectionPoint i.val =
      t₁ * G.weylPoint (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
    simpa only [G.weylPoint_eq] using h₁
  obtain ⟨t₂, ht₂, h₂⟩ := G.isBruhatSystem.weyl.weylElementPoint_mul G.rootBase w
    (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  have h₂' : G.weylPoint w * G.weylPoint (RootPairing.weylGroup.ofIdx G.rootSystem i.val) =
      t₂ * G.weylPoint (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
    simpa only [G.weylPoint_eq] using h₂
  let t₃ := G.weylPoint w * (t₀ * t₁) * (G.weylPoint w)⁻¹
  have ht₃ : t₃ ∈ G.torusPoints := by
    have h := (Subgroup.mem_normalizer_iff.mp (G.weylPoint_mem_normalizer w) (t₀ * t₁)).mp
      (G.torusPoints.mul_mem ht₀ ht₁)
    exact h
  refine ⟨t₃ * t₂, G.torusPoints.mul_mem ht₃ ht₂, ?_⟩
  calc
    G.weylPoint w * (G.reflectionPoint i.val)⁻¹ =
        t₃ * (G.weylPoint w * G.weylPoint
          (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) := by
      rw [h₀, h₁']
      dsimp only [t₃]
      group
    _ = _ := by rw [h₂']; group

/-- The inverse simple representative extends the chosen Weyl flag by its simple reflection. -/
theorem inverseSimple_flag (w : G.weylGroup) (i : G.rootBase.support) :
    flagProjection G (G.weylPoint w * (G.reflectionPoint i.val)⁻¹) =
      flagProjection G (G.weylPoint (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) := by
  obtain ⟨t, ht, he⟩ := inverseSimpleProduct G w i
  rw [he]
  apply (flagProjection_eq_iff G _ _).mpr
  have h := (Subgroup.mem_normalizer_iff''.mp
    (G.weylPoint_mem_normalizer (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) t).mp ht
  have hi := G.torusPoints.inv_mem h
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using G.torus_le_borel hi

end
end SchubertGeometry
