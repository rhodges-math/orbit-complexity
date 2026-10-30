import OrbitComplexity.SchubertGeometry.FlagVariety.Generation
import OrbitComplexity.ReductiveGroups.Groups.Cells.BruhatSubgroup
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBruhatSystem
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBruhatDisjoint
import Batteries.Tactic.Lint

/-! # Bruhat decomposition of reductive group points

The Bruhat union contains the open big cell and hence the whole group.
-/

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem longest_mem_bruhat :
    G.longestPoint ∈ G.isBruhatSystem.doubleCosetSubgroup := by
  refine ⟨G.longestElement, ?_⟩
  rw [← G.weylPoint_eq]
  exact ReductiveGroups.mem_subgroupDoubleCoset_self G.borelPoints G.longestPoint

private theorem oppositeUnipotent_le_bruhat :
    G.oppositeUnipotentPoints ≤ G.isBruhatSystem.doubleCosetSubgroup := by
  intro g hg
  let H := G.isBruhatSystem.doubleCosetSubgroup
  have hu : G.longestPoint⁻¹ * g * G.longestPoint ∈ G.unipotentPoints :=
    (G.conj_mem_oppositeUnipotent _).mp (by
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hg)
  have hb : G.longestPoint⁻¹ * g * G.longestPoint ∈ H :=
    G.isBruhatSystem.borel_le_doubleCosetSubgroup (G.unipotent_le_borel hu)
  have hw : G.longestPoint ∈ H := longest_mem_bruhat G
  have hm := H.mul_mem (H.mul_mem hw hb) (H.inv_mem hw)
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hm

private theorem bruhatSubgroup_eq_top : G.isBruhatSystem.doubleCosetSubgroup = ⊤ := by
  apply top_unique
  rw [← oppositeUnipotent_borel_generate G]
  exact sup_le (oppositeUnipotent_le_bruhat G)
    G.isBruhatSystem.borel_le_doubleCosetSubgroup

/-- Every group point lies in a Bruhat double coset. -/
theorem bruhatDecomposition (g : G.points) :
    ∃ w : G.weylGroup,
      g ∈ ReductiveGroups.subgroupDoubleCoset G.borelPoints (G.weylPoint w) := by
  have hg : g ∈ G.isBruhatSystem.doubleCosetSubgroup := by
    rw [bruhatSubgroup_eq_top]
    exact Subgroup.mem_top g
  obtain ⟨w, hw⟩ := hg
  exact ⟨w, by simpa only [G.weylPoint_eq] using hw⟩

/-- Two Bruhat double cosets containing the same group point have equal Weyl indices. -/
theorem bruhatDecomposition_unique {v w : G.weylGroup} {g : G.points}
    (hv : g ∈ ReductiveGroups.subgroupDoubleCoset G.borelPoints (G.weylPoint v))
    (hw : g ∈ ReductiveGroups.subgroupDoubleCoset G.borelPoints (G.weylPoint w)) : v = w := by
  apply G.isBruhatSystem.eq_of_doubleCoset_inter
    (fun a ha => G.eq_one_of_weylPoint_mem_borel a (by
      simpa only [G.weylPoint_eq] using ha))
  · simpa only [G.weylPoint_eq] using hv
  · simpa only [G.weylPoint_eq] using hw

/-- The adjoint stabilizer of the Borel tangent consists exactly of the Borel points. -/
theorem borelTangent_map_eq_iff (g : G.points) :
    G.borelTangent.toSubmodule.map (ReductiveGroups.affineGroupAdjointRepresentation g) =
      G.borelTangent.toSubmodule ↔ g ∈ G.borelPoints := by
  constructor
  · intro hg
    have hmul (a b : G.points)
        (ha : G.borelTangent.toSubmodule.map
          (ReductiveGroups.affineGroupAdjointRepresentation a) = G.borelTangent.toSubmodule)
        (hb : G.borelTangent.toSubmodule.map
          (ReductiveGroups.affineGroupAdjointRepresentation b) = G.borelTangent.toSubmodule) :
        G.borelTangent.toSubmodule.map
          (ReductiveGroups.affineGroupAdjointRepresentation (a * b)) =
            G.borelTangent.toSubmodule := by
      rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp, hb, ha]
    have hinv (a : G.points)
        (ha : G.borelTangent.toSubmodule.map
          (ReductiveGroups.affineGroupAdjointRepresentation a) = G.borelTangent.toSubmodule) :
        G.borelTangent.toSubmodule.map
          (ReductiveGroups.affineGroupAdjointRepresentation a⁻¹) =
            G.borelTangent.toSubmodule := by
      calc
        _ = (G.borelTangent.toSubmodule.map
            (ReductiveGroups.affineGroupAdjointRepresentation a)).map
              (ReductiveGroups.affineGroupAdjointRepresentation a⁻¹) :=
          congrArg (fun M : Submodule K G.tangent =>
            M.map (ReductiveGroups.affineGroupAdjointRepresentation a⁻¹)) ha.symm
        _ = _ := by
          rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel,
            map_one]
          exact Submodule.map_id _
    obtain ⟨w, b₁, hb₁, b₂, hb₂, hprod⟩ := bruhatDecomposition G g
    have hweyl : G.weylPoint w = b₁⁻¹ * g * b₂⁻¹ := by
      rw [hprod]
      group
    have hw : w = 1 := G.eq_one_of_weylPoint_adjoint w (by
      rw [hweyl]
      exact hmul _ _ (hmul _ _ (hinv _ (G.borelTangent_map_adjoint _ hb₁)) hg)
        (hinv _ (G.borelTangent_map_adjoint _ hb₂)))
    have hwB : G.weylPoint w ∈ G.borelPoints := by
      rw [hw, G.weylPoint_eq, ReductiveGroups.weylElementPoint_one]
      exact G.borelPoints.one_mem
    rw [hprod]
    exact G.borelPoints.mul_mem (G.borelPoints.mul_mem hb₁ hwB) hb₂
  · exact G.borelTangent_map_adjoint g

end
end SchubertGeometry
