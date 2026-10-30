import OrbitComplexity.SchubertGeometry.Parabolics.Projection
import OrbitComplexity.SchubertGeometry.FlagVariety.Proper
import OrbitComplexity.SchubertGeometry.FlagVariety.PointTopology
import OrbitComplexity.GroupActions.Varieties.Subvarieties
import OrbitComplexity.GroupActions.Varieties.OpenPoints
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Projectivity and point topology of partial flags

Properness descends from the complete flag variety along its surjective projection.
The projective orbit immersion is therefore closed. The parabolic-coset topology agrees
with the rational-point topology of the partial flag variety.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups SchubertGeometry Topology
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem proper_target (X Y : GroupActions.Variety K) (f : X.toOver ⟶ Y.toOver)
    [Surjective f.left] [IsProper X.toSpec] : IsProper Y.toSpec := by
  have hw : f.left ≫ Y.toSpec = X.toSpec := f.w
  have : UniversallyClosed (f.left ≫ Y.toSpec) := by rw [hw]; infer_instance
  have : UniversallyClosed Y.toSpec := UniversallyClosed.of_comp_surjective f.left Y.toSpec
  exact {}

/-- The projection from complete to standard partial flags is proper. -/
instance partialFlagMorphism_isProper (J : Set G.rootBase.support) :
    IsProper (partialFlagMorphism G J).left := by
  have hw : (partialFlagMorphism G J).left ≫ (partialFlagVariety G J).toSpec =
      (flagVariety G).toSpec := (partialFlagMorphism G J).w
  have : IsProper ((partialFlagMorphism G J).left ≫ (partialFlagVariety G J).toSpec) := by
    rw [hw]
    infer_instance
  exact IsProper.of_comp (partialFlagMorphism G J).left (partialFlagVariety G J).toSpec

/-- The standard partial flag variety is proper over the base field. -/
instance partialFlagVariety_isProper (J : Set G.rootBase.support) :
    IsProper (partialFlagVariety G J).toSpec :=
  proper_target (flagVariety G) (partialFlagVariety G J) (partialFlagMorphism G J)

/-- The standard partial flag variety is a closed subvariety of finite projective space. -/
theorem partialFlag_projective (J : Set G.rootBase.support) :
    ∃ n : ℕ, ∃ i : (partialFlagVariety G J).toOver ⟶
      (projectiveVariety K (ULift.{u} (Fin n))).toOver, IsClosedImmersion i.left := by
  obtain ⟨n, i, hi⟩ := partialFlag_quasiprojective G J
  let : IsImmersion i.left := hi
  have hw : i.left ≫ (projectiveVariety K (ULift.{u} (Fin n))).toSpec =
      (partialFlagVariety G J).toSpec := i.w
  have : IsProper (i.left ≫ (projectiveVariety K (ULift.{u} (Fin n))).toSpec) := by
    rw [hw]
    infer_instance
  have : IsProper i.left :=
    IsProper.of_comp i.left (projectiveVariety K (ULift.{u} (Fin n))).toSpec
  exact ⟨n, i, IsClosedImmersion.of_isPreimmersion i.left i.left.isClosedMap.isClosed_range⟩

omit [CharZero K] in
private theorem closedMap_points {X Y : GroupActions.Variety K} (f : X.toOver ⟶ Y.toOver)
    (hf : IsClosedMap f.left) : IsClosedMap (Variety.mapPoints f) := by
  intro U hU
  obtain ⟨V, hV, rfl⟩ := X.isEmbedding_pointMap.isClosed_iff.mp hU
  have he : Variety.mapPoints f '' (X.pointMap ⁻¹' V) =
      Y.pointMap ⁻¹' (f.left '' V) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨X.pointMap p, hp, Variety.pointMap_mapPoints f p⟩
    · rintro ⟨z, hzV, hzy⟩
      let Z : TopologicalSpace.Closeds X.scheme := ⟨V, hV⟩
      let g := X.closedInclusion Z ≫ f
      have hz : z ∈ Set.range (X.closedInclusion Z).left := by
        rw [X.closedInclusion_range Z]
        exact hzV
      obtain ⟨a, rfl⟩ := hz
      have hy : Y.pointMap y ∈ Set.range g.left := ⟨a, hzy⟩
      obtain ⟨p, hp⟩ := Variety.exists_mapPoints_eq g y hy
      refine ⟨Variety.mapPoints (X.closedInclusion Z) p, ?_, ?_⟩
      · change X.pointMap (Variety.mapPoints (X.closedInclusion Z) p) ∈ V
        rw [Variety.pointMap_mapPoints]
        have hm := Set.mem_range_self (f := (X.closedInclusion Z).left)
          ((X.closedSubvariety Z).pointMap p)
        rw [X.closedInclusion_range Z] at hm
        exact hm
      · exact (Variety.mapPoints_comp (X.closedInclusion Z) f p).symm.trans hp
  rw [he]
  exact (hf V hV).preimage Y.continuous_pointMap

private theorem pointsContinuous (J : Set G.rootBase.support) :
    Continuous (partialFlagPointsEquiv G J) := by
  have hq : IsQuotientMap (QuotientGroup.mk : G.points → partialFlagPoints G J) :=
    isQuotientMap_quotient_mk'
  apply hq.continuous_iff.mpr
  have he : (partialFlagPointsEquiv G J) ∘ QuotientGroup.mk =
      (Variety.mapPoints (partialFlagQuotient G J)) ∘ reductivePointsHomeomorph G :=
    funext (fun g => (partialFlagQuotient_points G J g).symm)
  rw [he]
  exact (Variety.continuous_mapPoints (partialFlagQuotient G J)).comp
    (reductivePointsHomeomorph G).continuous

private theorem pointsClosed (J : Set G.rootBase.support)
    (hπ : IsClosedMap (partialFlagMorphism G J).left) :
    IsClosedMap (partialFlagPointsEquiv G J) := by
  intro S hS
  have hpre := hS.preimage (partialFlagProjection_continuous G J)
  have hB := (flagVarietyPointsHomeomorph G).isClosedMap _ hpre
  have hP := closedMap_points (partialFlagMorphism G J) hπ _ hB
  have he : (Variety.mapPoints (partialFlagMorphism G J)) ∘ flagVarietyPointsEquiv G =
      partialFlagPointsEquiv G J ∘ partialFlagProjection G J :=
    funext (partialFlagMorphism_points G J)
  change IsClosed (Variety.mapPoints (partialFlagMorphism G J) ''
    (flagVarietyPointsEquiv G '' (partialFlagProjection G J ⁻¹' S))) at hP
  rw [← Set.image_comp, he, Set.image_comp,
    Set.image_preimage_eq S (partialFlagProjection_surjective G J)] at hP
  exact hP

/-- Parabolic cosets and rational partial flag points have the same Zariski topology. -/
def partialFlagPointsHomeomorph (J : Set G.rootBase.support) :
    partialFlagPoints G J ≃ₜ (partialFlagVariety G J).points :=
  (partialFlagPointsEquiv G J).toHomeomorphOfContinuousClosed
    (pointsContinuous G J) (pointsClosed G J (partialFlagMorphism G J).left.isClosedMap)

end SchubertGeometry
