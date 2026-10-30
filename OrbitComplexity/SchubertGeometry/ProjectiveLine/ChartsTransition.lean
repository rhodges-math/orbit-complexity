import OrbitComplexity.SchubertGeometry.ProjectiveLine.ChartsOverlap
import OrbitComplexity.GroupActions.Varieties.AdditiveOpens
import OrbitComplexity.GroupActions.Varieties.CoordinateInversion

/-! # Scheme overlap and transition of the rank-one charts

The inverse image of the negative chart in the positive chart is the punctured additive
line. Regular inversion on that line identifies the two chart morphisms.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups TauCeti TopologicalSpace
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The inverse image of the negative chart is the punctured positive chart. -/
theorem simpleCharts_overlap_open (i : G.rootBase.support) :
    (simplePositiveChart G i).left ⁻¹' Set.range (simpleNegativeChart G i).left =
      (additiveNonzero K : Set (additiveVariety K).scheme) := by
  have : JacobsonSpace (additiveVariety K).toOver.left :=
    LocallyOfFiniteType.jacobsonSpace (additiveVariety K).toSpec
  have : IsNoetherian (additiveVariety K).toOver.left := Variety.noetherian _
  have hU : IsOpen ((simplePositiveChart G i).left ⁻¹'
      Set.range (simpleNegativeChart G i).left) :=
    (simpleNegativeChart G i).left.isOpenEmbedding.isOpen_range.preimage
      (simplePositiveChart G i).left.continuous
  apply constructible_eq ((NoetherianSpace.isCompact _).isConstructible hU)
    ((NoetherianSpace.isCompact _).isConstructible (additiveNonzero K).isOpen)
  ext p
  by_cases hp : IsClosed ({p} : Set (additiveVariety K).scheme)
  · have hp' : p ∈ Set.range (additiveVariety K).pointMap := by
      rw [Variety.pointMap_range]
      exact hp
    obtain ⟨q, rfl⟩ := hp'
    have hov := simpleCharts_overlap G i ((additivePointsEquiv K).symm q)
    rw [Equiv.apply_symm_apply, Variety.range_mapPoints] at hov
    simp only [Set.mem_preimage] at hov
    rw [Variety.pointMap_mapPoints] at hov
    constructor
    · rintro ⟨hq, hc⟩
      exact ⟨(mem_additiveNonzero K q).mpr (hov.mp hq), hc⟩
    · rintro ⟨hq, hc⟩
      exact ⟨hov.mpr ((mem_additiveNonzero K q).mp hq), hc⟩
  · change (_ ∧ IsClosed ({p} : Set (additiveVariety K).scheme)) ↔
      (_ ∧ IsClosed ({p} : Set (additiveVariety K).scheme))
    simp only [hp, and_false]

/-- The two punctured chart morphisms agree after regular inversion of the parameter. -/
theorem simpleCharts_transition_comp (i : G.rootBase.support) :
    (additiveVariety K).openInclusion (additiveNonzero K) ≫ simplePositiveChart G i =
      (puncturedAdditiveInvIso K).hom ≫
        (additiveVariety K).openInclusion (additiveNonzero K) ≫ simpleNegativeChart G i := by
  apply Variety.mapPoints_injective
  funext p
  let t := (additivePointsEquiv K).symm (Variety.mapPoints
    ((additiveVariety K).openInclusion (additiveNonzero K)) p)
  have ht : t ≠ 0 := by
    change Variety.mapPoints ((additiveVariety K).openInclusion (additiveNonzero K)) p ∈
      {x | (additivePointsEquiv K).symm x ≠ 0}
    rw [← additiveNonzero_points K]
    exact ⟨p, rfl⟩
  have hp0 : Variety.mapPoints ((additiveVariety K).openInclusion (additiveNonzero K)) p =
      additivePointsEquiv K t := (Equiv.apply_symm_apply _ _).symm
  have hp1 : Variety.mapPoints ((additiveVariety K).openInclusion (additiveNonzero K))
      (Variety.mapPoints (puncturedAdditiveInvIso K).hom p) =
        additivePointsEquiv K t⁻¹ := by
    apply (additivePointsEquiv K).symm.injective
    rw [Equiv.symm_apply_apply]
    exact puncturedAdditiveInvIso_points K p
  simp only [Variety.mapPoints_comp]
  rw [hp0, hp1]
  exact simpleCharts_transition G i ht
end SchubertGeometry
