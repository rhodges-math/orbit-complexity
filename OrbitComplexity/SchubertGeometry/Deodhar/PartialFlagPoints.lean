import OrbitComplexity.SchubertGeometry.Deodhar.CellProjection

/-! # Rational points of rank-one partial flags

The Borel and its simple double coset form a subgroup. At an increasing simple step,
projection to its coset space is injective on the preceding Schubert cell.
-/

open ReductiveGroups
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
  (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))


/-- The rank-one parabolic subgroup is the Borel together with its simple double coset. -/
def rankOneParabolicPoints : Subgroup G.points where
  carrier := rankOneParabolic G.borelPoints (G.reflectionPoint i.val)
  one_mem' := Or.inl G.borelPoints.one_mem
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha | ha
    · exact IsRankOneBruhatData.mul_mem_parabolic ha hb
    · rcases hb with hb | hb
      · exact IsRankOneBruhatData.parabolic_mul_mem (Or.inr ha) hb
      · exact (G.isBruhatSystem.rankOne i).doubleCoset_mul ha hb
  inv_mem' := fun ha => (G.isBruhatSystem.rankOne i).parabolic_inv ha

/-- The Borel coset of a point determines its rank-one parabolic coset. -/
def rankOnePartialProjection : flagPoints G → G.points ⧸ rankOneParabolicPoints G i :=
  Quotient.lift (fun g => (QuotientGroup.mk g : G.points ⧸ rankOneParabolicPoints G i))
    (fun _ _ h => QuotientGroup.eq.mpr (Or.inl (QuotientGroup.leftRel_apply.mp h)))

/-- Equality of partial flags is membership of the quotient in the rank-one parabolic. -/
theorem rankOnePartialProjection_eq (g h : G.points) :
    rankOnePartialProjection G i (flagProjection G g) =
      rankOnePartialProjection G i (flagProjection G h) ↔
        g⁻¹ * h ∈ rankOneParabolicPoints G i := QuotientGroup.eq
include hw in
/-- An increasing Schubert cell meets each rank-one partial flag in at most one flag. -/
theorem rankOneBase_unique (g h : G.points)
    (hg : g ∈ subgroupDoubleCoset G.borelPoints (G.weylPoint w))
    (hh : h ∈ subgroupDoubleCoset G.borelPoints (G.weylPoint w))
    (hrel : g⁻¹ * h ∈ rankOneParabolic G.borelPoints (G.reflectionPoint i.val)) :
    flagProjection G g = flagProjection G h := by
  rcases hrel with hb | hd
  · exact (flagProjection_eq_iff G g h).mpr hb
  · have hprod := G.isBruhatSystem.doubleCoset_mul_of_isPos w i hw
      (by simpa only [G.weylPoint_eq] using hg) hd
    have hnew : h ∈ subgroupDoubleCoset G.borelPoints
        (G.weylPoint (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) := by
      simpa only [G.weylPoint_eq, mul_inv_cancel_left] using hprod
    have he := bruhatDecomposition_unique G hh hnew
    have hs : (weylCoxeterSystem G.rootBase).simple i = 1 := by
      rw [weylCoxeterSystem_simple]
      exact (mul_left_cancel ((mul_one w).trans he)).symm
    have hlen := congrArg (weylCoxeterSystem G.rootBase).length hs
    exact (Nat.one_ne_zero (by simpa only [CoxeterSystem.length_simple,
      CoxeterSystem.length_one] using hlen)).elim

/-- Projection to rank-one partial flags commutes with left multiplication. -/
theorem rankOnePartial_smul (g : G.points) (q : flagPoints G) :
    rankOnePartialProjection G i (g • q) = g • rankOnePartialProjection G i q := by
  obtain ⟨h, rfl⟩ := flagProjection_surjective G q
  rfl

include hw in
/-- Rank-one partial projection is injective on the preceding Schubert orbit at an ascent. -/
theorem rankOnePartial_injOn : Set.InjOn (rankOnePartialProjection G i)
    {q | flagVarietyPointsEquiv G q ∈
      MulAction.orbit (GroupActions.borelVariety G).points (weylFlagPoint G w)} := by
  intro q hq r hr hqr
  obtain ⟨g, rfl⟩ := flagProjection_surjective G q
  obtain ⟨h, rfl⟩ := flagProjection_surjective G r
  exact rankOneBase_unique G w i hw g h ((mem_schubertOrbit_iff G w g).mp hq)
    ((mem_schubertOrbit_iff G w h).mp hr) ((rankOnePartialProjection_eq G i g h).mp hqr)
end
end SchubertGeometry
