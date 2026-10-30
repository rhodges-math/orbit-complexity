import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.LeftUnipotent
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.RankoneFrames
import OrbitComplexity.SchubertGeometry.Deodhar.OppositeRootPoints

/-! # simple-Gauss restrictions of the full determinant coefficient -/

open ReductiveGroups TauCeti GroupActions

noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem negative_mem (i : G.rootBase.support) (t : K) :
    gaParameterPoint (G.negativeSimpleRootMap i) t ∈ G.oppositeUnipotentPoints := by
  have htr : G.rootPointTransport (1 : G.points)
      (G.rootSystem.weylGroupToPerm (1 : G.weylGroup)) := by
    simpa only [map_one] using G.isBruhatSystem.weyl.transport_one
  have hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm (1 : G.weylGroup) i.val) := by
    simpa only [map_one, Equiv.Perm.one_apply] using
      G.rootBase.isPos_of_mem_support i.property
  simpa only [one_mul, mul_one, inv_one] using
    negativeSimple_conj_opposite G 1 1 htr i hi t

private theorem positive_mem (i : G.rootBase.support) (t : K) :
    gaParameterPoint (G.simpleRootMap i) t ∈ G.unipotentPoints := by
  apply GaParameterPoint.mem_of_tangent_mem_quotient _ _ ?_ t
  exact (G.rootWeightSpace_le_unipotent i.val
    (G.rootBase.isPos_of_mem_support i.property)) (G.simpleRootMap_tangent_mem i)

private theorem positive_character_coroot (i : G.rootBase.support) (a : Kˣ) :
    (Coroot.simpleCorootTorusPoint G i a).ofConv
      (MonoidAlgebra.single G.positiveRootCharacter 1) = (a : K) ^ 2 := by
  have he : G.oddRootCharacter 3 = G.positiveRootCharacter := by
    simp only [ReductiveGroupData.oddRootCharacter, Nat.reduceSub, Nat.reduceDiv, pow_one]
  have h := G.oddRootCharacter_eval 3 (by decide) i a
  rw [he] at h
  exact h.trans (Units.val_pow_eq_pow_val a 2)

private theorem positive_right (g : G.points) (i : G.rootBase.support) (t : K) :
    (g * gaParameterPoint (G.simpleRootMap i) t).ofConv (positiveDetCoefficient G) =
      g.ofConv (positiveDetCoefficient G) :=
  positiveDet_right_unipotent G g (gaParameterPoint (G.simpleRootMap i) t)
    (positive_mem G i t)

/-- On the negative simple-root frame the coefficient is identically one. -/
theorem positiveDet_negative_simple (i : G.rootBase.support) (t : K) :
    (gaParameterPoint (G.negativeSimpleRootMap i) t).ofConv (positiveDetCoefficient G) = 1 := by
  have h := positiveDet_left_unipotent G _ 1 (negative_mem G i t)
  have h1 : (1 : G.points).ofConv (positiveDetCoefficient G) = 1 := positiveDet_counit G
  simpa only [mul_one, h1] using h

set_option maxHeartbeats 400000 in
/-- The simple-Gauss decomposition gives the exact squared coordinate,
with the chosen inverse normalizer and no omitted sign or scalar. -/
theorem positiveDet_simpleGauss_unit (i : G.rootBase.support) (a : Kˣ) :
    (gaParameterPoint (G.simpleRootMap i) (a : K) *
      (G.reflectionPoint i.val)⁻¹).ofConv (positiveDetCoefficient G) = (a : K) ^ 2 := by
  have htor : (Coroot.simpleCorootPoint G i a).ofConv (positiveDetCoefficient G) =
      (a : K) ^ 2 := by
    have h := positiveDet_right_torus G 1 (Coroot.simpleCorootTorusPoint G i a)
    have h1 : (1 : G.points).ofConv (positiveDetCoefficient G) = 1 := positiveDet_counit G
    simpa only [one_mul, h1, mul_one, Coroot.simpleCorootPoint,
      positive_character_coroot G i a] using h
  have hframe := congrArg (fun g : G.points => g.ofConv (positiveDetCoefficient G))
    (simpleFrame_overlap G i a).symm
  have hneg := positiveDet_left_unipotent G
    (gaParameterPoint (G.negativeSimpleRootMap i) (↑(a⁻¹) : K))
    (Coroot.simpleCorootPoint G i a *
      gaParameterPoint (G.simpleRootMap i) (-↑(a⁻¹) : K))
    (negative_mem G i (↑(a⁻¹) : K))
  have hpos := positive_right G (Coroot.simpleCorootPoint G i a) i (-↑(a⁻¹) : K)
  exact hframe.trans (hneg.trans (hpos.trans htor))

end SchubertGeometry.DeterminantSection
