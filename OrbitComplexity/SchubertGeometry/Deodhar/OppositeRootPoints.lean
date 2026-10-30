import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupOppositeTangent
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaConjugateTangent


/-! # Opposite-root membership under Weyl transport

Conjugation carries a simple additive root subgroup into the opposite unipotent whenever
its transported tangent root is negative.
-/

open ReductiveGroups TauCeti
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem rootGa_conj_opposite (n : G.points) (w : G.weylGroup)
    (htr : G.rootPointTransport n (G.rootSystem.weylGroupToPerm w))
    (x : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K) (r : G.rootIndex)
    (hx : gaAffineGroupTangent x ∈ G.rootWeightSpace r)
    (hr : ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w r)) (t : K) :
    n * gaParameterPoint x t * n⁻¹ ∈ G.oppositeUnipotentPoints := by
  have hm : affineGroupAdjointLieEquiv n (gaAffineGroupTangent x) ∈
      (G.rootWeightSpace r).map (affineGroupAdjointLieEquiv n).toLinearEquiv.toLinearMap :=
    Submodule.mem_map.mpr ⟨_, hx, rfl⟩
  rw [htr r] at hm
  have hle : G.rootWeightSpace (G.rootSystem.weylGroupToPerm w r) ≤
      G.oppositeUnipotentTangent.toSubmodule := by
    rw [G.oppositeUnipotentTangent_eq_sum]
    exact le_iSup₂_of_le (G.rootSystem.weylGroupToPerm w r) hr le_rfl
  have hp := GaParameterPoint.mem_of_tangent_mem_quotient
    (x.comp (affineGroupConjugationBialgHom n)) G.oppositeUnipotentIdeal
    (by rw [gaTangent_comp_conjugation]; exact hle hm) t
  have hc := gaPoints_comp_conjugation x n (Multiplicative.ofAdd t)
  change gaParameterPoint _ t = n * gaParameterPoint x t * n⁻¹ at hc
  rw [← hc]
  exact hp

private theorem rootPerm_neg (w : G.weylGroup) (r : G.rootIndex) :
    G.rootSystem.weylGroupToPerm w (-r) = -G.rootSystem.weylGroupToPerm w r := by
  apply G.rootSystem.root.injective
  rw [← G.rootSystem.weylGroup_apply_root]
  change w • (-G.rootSystem.root r) = -G.rootSystem.root (G.rootSystem.weylGroupToPerm w r)
  rw [smul_neg, G.rootSystem.weylGroup_apply_root]

/-- A transported negative simple root lies in the opposite unipotent at an ascent. -/
theorem negativeSimple_conj_opposite (n : G.points) (w : G.weylGroup)
    (htr : G.rootPointTransport n (G.rootSystem.weylGroupToPerm w))
    (i : G.rootBase.support) (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val))
    (t : K) : n * gaParameterPoint (G.negativeSimpleRootMap i) t * n⁻¹ ∈
      G.oppositeUnipotentPoints := by
  apply rootGa_conj_opposite G n w htr (G.negativeSimpleRootMap i) (-i.val)
    (G.negativeRootMap_tangent_mem i) ?_ t
  rw [rootPerm_neg]
  intro hn
  have hn' : G.rootBase.IsPos (G.rootSystem.reflectionPerm
      (G.rootSystem.weylGroupToPerm w i.val) (G.rootSystem.weylGroupToPerm w i.val)) := by
    simpa only [LieAlgebra.IsKilling.rootSystem_reflectionPerm_self_eq_neg] using hn
  exact (isPos_neg_index_iff G.rootBase _).mp hn' hi

/-- A transported positive simple root lies in the opposite unipotent at a descent. -/
theorem positiveSimple_conj_opposite (n : G.points) (w : G.weylGroup)
    (htr : G.rootPointTransport n (G.rootSystem.weylGroupToPerm w))
    (i : G.rootBase.support) (hi : ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val))
    (t : K) : n * gaParameterPoint (G.simpleRootMap i) t * n⁻¹ ∈
      G.oppositeUnipotentPoints :=
  rootGa_conj_opposite G n w htr (G.simpleRootMap i) i.val (G.simpleRootMap_tangent_mem i) hi t

end
end SchubertGeometry
