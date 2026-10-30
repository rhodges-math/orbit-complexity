import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBraidFourCommute

/-! # An adjacent short representative square centralizes the long rank-one group -/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
  (G : ReductiveGroupData K)

private theorem square_parameter_commute (j : G.rootBase.support)
    (r : G.rootIndex) (x : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hx : gaAffineGroupTangent x ∈ G.rootWeightSpace r)
    (hp : (-1 : K) ^ G.rootSystem.pairingIn ℤ r j.val = 1) (a : K) :
    Commute ((G.reflectionPoint j.val) ^ 2) (gaParameterPoint x a) := by
  have he : affineGroupAdjointRepresentation ((G.reflectionPoint j.val) ^ 2)
      (gaAffineGroupTangent x) = (1 : K) • gaAffineGroupTangent x := by
    rw [G.simpleReflection_square_weight j r _ hx, hp]
  have hc := GaAffineGroupPoints.conjugate_of_tangent_eq x x
    ((G.reflectionPoint j.val) ^ 2) 1 he a
  change (G.reflectionPoint j.val) ^ 2 * gaParameterPoint x a *
    ((G.reflectionPoint j.val) ^ 2)⁻¹ = gaParameterPoint x ((1 : K) * a) at hc
  rw [one_mul] at hc
  show (G.reflectionPoint j.val) ^ 2 * gaParameterPoint x a =
    gaParameterPoint x a * (G.reflectionPoint j.val) ^ 2
  calc
    _ = ((G.reflectionPoint j.val) ^ 2 * gaParameterPoint x a *
        ((G.reflectionPoint j.val) ^ 2)⁻¹) * (G.reflectionPoint j.val) ^ 2 := by group
    _ = _ := by rw [hc]

/-- The short simple representative square centralizes the adjacent long representative. -/
theorem reflection_square_commute (i j : G.rootBase.support)
    (hp : G.rootSystem.pairingIn ℤ i.val j.val = -2) :
    Commute (G.reflectionPoint i.val) ((G.reflectionPoint j.val) ^ 2) := by
  have hn : G.rootSystem.reflectionPerm i.val i.val = -i.val := by
    apply G.rootSystem.root.injective
    rw [G.rootSystem.root_reflectionPerm, G.rootSystem.reflection_apply_self]
    rfl
  have hpneg : G.rootSystem.pairingIn ℤ (-i.val) j.val = 2 := by
    rw [← hn, G.rootSystem.pairingIn_reflectionPerm_self_left, hp]
    norm_num
  have he := square_parameter_commute G j i.val (G.simpleRootMap i)
    (G.simpleRootMap_tangent_mem i) (by rw [hp]; norm_num) 1
  have hf := square_parameter_commute G j (-i.val) (G.negativeSimpleRootMap i)
    (G.negativeRootMap_tangent_mem i) (by rw [hpneg]; norm_num) (-1)
  exact ((he.mul_right hf).mul_right he).symm

end ReductiveGroups.ReductiveGroupData
