import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupOppositeTangent
import OrbitComplexity.ReductiveGroups.Groups.Exponential.BorelRootExponentialBijection
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaConjugate
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaPointSubgroup

/-!
# The opposite unipotent subgroup meets the Borel subgroup in the identity

Every opposite unipotent point is the parameter-one point of a conjugated
additive one-parameter subgroup. Membership of this point in the Borel forces
its tangent into both complementary tangent subspaces. The tangent is zero,
so the one-parameter subgroup and the original point are trivial.
-/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open TauCeti

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- A rational point lying in both the opposite unipotent and Borel subgroups is the identity. -/
theorem eq_one_of_oppositeUnipotent_borel (g : G.points)
    (hU : g ∈ G.oppositeUnipotentPoints) (hB : g ∈ G.borelPoints) : g = 1 := by
  let x := G.longestPoint⁻¹ * g * G.longestPoint
  have hx : x ∈ G.unipotentPoints := by
    apply (G.conj_mem_oppositeUnipotent x).mp
    simpa only [x, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hU
  obtain ⟨φ, hφ, _⟩ := BorelRootExponentialBijection.existsUnique_of_borelRootUnipotentPoint
    G.borelIdeal G.isBorel G.torusSplit G.split_surjective x hx
  let ψ := φ.comp (affineGroupConjugationBialgHom G.longestPoint)
  have hψ : gaAffineGroupPoints ψ (Multiplicative.ofAdd (1 : K)) = g := by
    rw [gaPoints_comp_conjugation, hφ]
    simp only [x, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  rw [← hψ]
  exact gaPoint_one_eq_one_of_disjoint ψ G.oppositeUnipotentIdeal G.borelIdeal
    G.oppositeUnipotent_disjoint_borel
    (by simpa only [hψ, oppositeUnipotentPoints] using hU)
    (by simpa only [hψ, borelPoints] using hB)

/-- The rational-point subgroups of the opposite unipotent and Borel groups are disjoint. -/
theorem oppositeUnipotentPoints_disjoint :
    Disjoint G.oppositeUnipotentPoints G.borelPoints := by
  apply disjoint_iff.mpr
  apply le_antisymm ?_ bot_le
  intro g hg
  exact G.eq_one_of_oppositeUnipotent_borel g hg.1 hg.2

end ReductiveGroupData
