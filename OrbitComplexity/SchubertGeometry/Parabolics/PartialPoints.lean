import OrbitComplexity.SchubertGeometry.Parabolics.DoubleCosets
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicDecomposition

/-! # Rational points of standard partial flags

The Borel-to-parabolic coset projection is open, continuous, surjective and equivariant.
Its Weyl flags agree exactly on right parabolic Weyl cosets. Minimal right Weyl
representatives therefore give distinct partial flags.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Rational partial flag points are the cosets of the standard parabolic point subgroup. -/
abbrev partialFlagPoints (J : Set G.rootBase.support) :=
  G.points ⧸ standardParabolicPoints G J

/-- The Borel coset projection to the prescribed standard parabolic coset space. -/
def partialFlagProjection (J : Set G.rootBase.support) : flagPoints G → partialFlagPoints G J :=
  Subgroup.quotientMapOfLE (show G.borelPoints ≤ standardParabolicPoints G J from le_sup_left)

/-- Equality of projected flags is membership of their quotient in the standard parabolic. -/
theorem partialFlagProjection_eq (J : Set G.rootBase.support) (g h : G.points) :
    partialFlagProjection G J (flagProjection G g) =
      partialFlagProjection G J (flagProjection G h) ↔
        g⁻¹ * h ∈ standardParabolicPoints G J := QuotientGroup.eq

/-- Every standard parabolic coset is the image of a Borel coset. -/
theorem partialFlagProjection_surjective (J : Set G.rootBase.support) :
    Function.Surjective (partialFlagProjection G J) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨flagProjection G g, rfl⟩

/-- The partial flag projection commutes with left translation by group points. -/
theorem partialFlagProjection_smul (J : Set G.rootBase.support)
    (g : G.points) (q : flagPoints G) :
    partialFlagProjection G J (g • q) = g • partialFlagProjection G J q := by
  obtain ⟨h, rfl⟩ := flagProjection_surjective G q
  rfl

/-- The partial flag projection is continuous for the quotient Zariski topologies. -/
theorem partialFlagProjection_continuous (J : Set G.rootBase.support) :
    Continuous (partialFlagProjection G J) := by
  apply (flagProjection_quotientMap G).continuous_iff.mpr
  change Continuous (QuotientGroup.mk : G.points → partialFlagPoints G J)
  exact continuous_quot_mk

/-- The partial flag projection is open for the quotient Zariski topologies. -/
theorem partialFlagProjection_isOpenMap (J : Set G.rootBase.support) :
    IsOpenMap (partialFlagProjection G J) := by
  apply IsOpenMap.of_comp (continuous_flagProjection G) (flagProjection_surjective G)
  change IsOpenMap (QuotientGroup.mk : G.points → partialFlagPoints G J)
  exact QuotientGroup.isOpenMap_coe (N := standardParabolicPoints G J)

private theorem inverse_weyl_product (u v : G.weylGroup) :
    (G.weylPoint u)⁻¹ * G.weylPoint v ∈ subgroupDoubleCoset G.borelPoints
      (G.weylPoint (u⁻¹ * v)) := by
  obtain ⟨a, ha, hea⟩ := G.isBruhatSystem.weyl.weylElementPoint_inv G.rootBase u
  obtain ⟨b, hb, heb⟩ := G.isBruhatSystem.weyl.weylElementPoint_mul G.rootBase u⁻¹ v
  change (G.weylPoint u)⁻¹ = a * G.weylPoint u⁻¹ at hea
  change G.weylPoint u⁻¹ * G.weylPoint v = b * G.weylPoint (u⁻¹ * v) at heb
  refine ⟨a * b, G.torus_le_borel (G.torusPoints.mul_mem ha hb), 1,
    G.borelPoints.one_mem, ?_⟩
  rw [hea, mul_assoc, heb]
  group

/-- Two Weyl flags have the same partial projection exactly when their Weyl cosets agree. -/
theorem partialWeylFlag_eq_iff (J : Set G.rootBase.support) (u v : G.weylGroup) :
    partialFlagProjection G J (flagProjection G (G.weylPoint u)) =
      partialFlagProjection G J (flagProjection G (G.weylPoint v)) ↔
        u⁻¹ * v ∈ standardParabolicSubgroup G.rootBase J := by
  rw [partialFlagProjection_eq]
  have hd := inverse_weyl_product G u v
  constructor
  · intro hmem
    change (G.weylPoint u)⁻¹ * G.weylPoint v ∈
      (standardParabolicPoints G J : Set G.points) at hmem
    rw [(standardParabolicPoints_bruhat G J).1] at hmem
    obtain ⟨a, ha, hda⟩ := Set.mem_iUnion₂.mp hmem
    exact (bruhatDecomposition_unique G hd hda).symm ▸ ha
  · intro huv
    change (G.weylPoint u)⁻¹ * G.weylPoint v ∈
      (standardParabolicPoints G J : Set G.points)
    rw [(standardParabolicPoints_bruhat G J).1]
    exact Set.mem_iUnion₂.mpr ⟨u⁻¹ * v, huv, hd⟩

/-- Distinct minimal right Weyl representatives give distinct partial Weyl flags. -/
theorem partialWeylFlag_injOn (J : Set G.rootBase.support) :
    Set.InjOn (fun w : G.weylGroup =>
      partialFlagProjection G J (flagProjection G (G.weylPoint w)))
        {w | IsMinimalRightParabolic G.rootBase J w} := by
  intro u hu v hv he
  have hmem := (partialWeylFlag_eq_iff G J u v).mp he
  exact (minimalRightParabolic_eq_of_mul G.rootBase J u v (u⁻¹ * v) hu hv hmem
    (by simp)).symm

end SchubertGeometry
