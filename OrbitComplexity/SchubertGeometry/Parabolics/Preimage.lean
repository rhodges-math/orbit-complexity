import OrbitComplexity.SchubertGeometry.Parabolics.Schubert
import OrbitComplexity.SchubertGeometry.Parabolics.ProjectionSmooth
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
import OrbitComplexity.SchubertGeometry.Parabolics.Proper
import OrbitComplexity.SchubertGeometry.Parabolics.SchubertPreimage

/-! # Schubert preimages under parabolic projection

Partial Schubert closures agree with their parabolic-coset closures. Their inverse
images in complete flags carry the Schubert scheme structure with longest parabolic suffix.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups
open SchubertGeometry Topology
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem cell_preimage (J : Set G.rootBase.support) (w : G.weylGroup) :
    (partialFlagPointsHomeomorph G J) ⁻¹'
      Set.range (Variety.mapPoints (partialSchubertCellInclusion G J w)) =
      MulAction.orbit G.borelPoints
        (partialFlagProjection G J (flagProjection G (G.weylPoint w))) := by
  rw [partialSchubertCell_points_range]
  ext q
  constructor
  · intro hq
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hq
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨borelPointsMulEquiv G b, ?_⟩
    apply (partialFlagPointsEquiv G J).injective
    change partialFlagPointsEquiv G J
      ((borelPointsMulEquiv G b : G.points) •
        partialFlagProjection G J (flagProjection G (G.weylPoint w))) = _
    rw [← borelPartialFlag_smul]
    exact hb
  · intro hq
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hq
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨(borelPointsMulEquiv G).symm b, ?_⟩
    change (borelPointsMulEquiv G).symm b • partialFlagPointsEquiv G J
      (partialFlagProjection G J (flagProjection G (G.weylPoint w))) =
        partialFlagPointsEquiv G J q
    rw [borelPartialFlag_smul, MulEquiv.apply_symm_apply]
    exact congrArg (partialFlagPointsEquiv G J) hb

private theorem closure_points (J : Set G.rootBase.support) (w : G.weylGroup) :
    Set.range (Variety.mapPoints (partialSchubertInclusion G J w)) =
      closure (Set.range (Variety.mapPoints (partialSchubertCellInclusion G J w))) := by
  rw [(partialFlagVariety G J).isEmbedding_pointMap.closure_eq_preimage_closure_image]
  change _ = (partialFlagVariety G J).pointMap ⁻¹' (partialFlagVariety G J).pointClosure _
  rw [(partialSchubertCell G J w).pointClosure_range, Variety.range_mapPoints,
    partialSchubertInclusion_range]

/-- The rational image of a partial Schubert variety agrees with its coset closure. -/
theorem partialSchubert_points (J : Set G.rootBase.support) (w : G.weylGroup) :
    (partialFlagPointsHomeomorph G J) ⁻¹'
      Set.range (Variety.mapPoints (partialSchubertInclusion G J w)) =
      partialSchubertPoints G J w := by
  rw [closure_points, Homeomorph.preimage_closure, cell_preimage]
  rfl

private theorem rational_preimage (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    (Variety.mapPoints (partialFlagMorphism G J)) ⁻¹'
        Set.range (Variety.mapPoints (partialSchubertInclusion G J w)) =
      Set.range (Variety.mapPoints
        (schubertInclusion G (w * longestParabolicElement G.rootBase J))) := by
  apply (Set.preimage_injective.mpr (flagVarietyPointsEquiv G).surjective)
  ext q
  change Variety.mapPoints (partialFlagMorphism G J) (flagVarietyPointsEquiv G q) ∈
    Set.range (Variety.mapPoints (partialSchubertInclusion G J w)) ↔
      flagVarietyPointsEquiv G q ∈ Set.range (Variety.mapPoints
        (schubertInclusion G (w * longestParabolicElement G.rootBase J)))
  rw [partialFlagMorphism_points]
  change partialFlagProjection G J q ∈ (partialFlagPointsHomeomorph G J) ⁻¹'
    Set.range (Variety.mapPoints (partialSchubertInclusion G J w)) ↔
      flagVarietyPointsEquiv G q ∈ Set.range (Variety.mapPoints
        (schubertInclusion G (w * longestParabolicElement G.rootBase J)))
  rw [partialSchubert_points]
  exact Set.ext_iff.mp (partialSchubert_preimage G J w hw) q

omit [CharZero K] in
private theorem closed_eq_of_points (X : GroupActions.Variety K) (S T : Set X.scheme)
    (hS : IsClosed S) (hT : IsClosed T) (h : X.pointMap ⁻¹' S = X.pointMap ⁻¹' T) :
    S = T := by
  have : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  have he : S ∩ closedPoints X.scheme = T ∩ closedPoints X.scheme := by
    rw [← X.pointMap_range, ← Set.image_preimage_eq_inter_range,
      ← Set.image_preimage_eq_inter_range, h]
  exact (closure_inter_closedPoints hS).symm.trans
    ((congrArg closure he).trans (closure_inter_closedPoints hT))

private theorem scheme_preimage (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    (partialFlagMorphism G J).left ⁻¹' Set.range (partialSchubertInclusion G J w).left =
      Set.range (schubertInclusion G (w * longestParabolicElement G.rootBase J)).left := by
  apply closed_eq_of_points (flagVariety G)
  · exact (partialSchubertInclusion G J w).left.isClosedMap.isClosed_range.preimage
      (partialFlagMorphism G J).left.continuous
  · have hclosed := (schubertInclusion G
        (w * longestParabolicElement G.rootBase J)).left.isClosedMap
    exact hclosed.isClosed_range
  · have hp := rational_preimage G J w hw
    rw [Variety.range_mapPoints, Variety.range_mapPoints] at hp
    simpa only [Set.preimage_preimage, Function.comp_def, Variety.pointMap_mapPoints] using hp

private def reducedRangeIso {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsPreimmersion f] [IsPreimmersion g] [IsReduced X] [IsReduced Y]
    (h : Set.range f = Set.range g) : X ≅ Y where
  hom := liftPreimmersion g f h.le
  inv := liftPreimmersion f g h.ge
  hom_inv_id := (cancel_mono f).mp (by
    simp only [Category.assoc, liftPreimmersion_fac, Category.id_comp])
  inv_hom_id := (cancel_mono g).mp (by
    simp only [Category.assoc, liftPreimmersion_fac, Category.id_comp])

/-- A partial Schubert preimage is the Schubert scheme with longest parabolic suffix. -/
theorem partialSchubert_pullback (J : Set G.rootBase.support) (w : G.weylGroup) :
    IsMinimalRightParabolic G.rootBase J w →
      ((partialFlagMorphism G J).left ⁻¹' Set.range (partialSchubertInclusion G J w).left =
        Set.range (schubertInclusion G (w * longestParabolicElement G.rootBase J)).left) ∧
      ∃ e : (schubertVariety G (w * longestParabolicElement G.rootBase J)).scheme ≅
          pullback (partialFlagMorphism G J).left (partialSchubertInclusion G J w).left,
        e.hom ≫ pullback.fst (partialFlagMorphism G J).left
            (partialSchubertInclusion G J w).left =
          (schubertInclusion G (w * longestParabolicElement G.rootBase J)).left := by
  intro hw
  have hpre := scheme_preimage G J w hw
  refine ⟨hpre, ?_⟩
  let p : (flagVariety G).scheme ⟶ (partialFlagVariety G J).scheme :=
    (partialFlagMorphism G J).left
  let i : (partialSchubertVariety G J w).scheme ⟶ (partialFlagVariety G J).scheme :=
    (partialSchubertInclusion G J w).left
  let f : (schubertVariety G (w * longestParabolicElement G.rootBase J)).scheme ⟶
      (flagVariety G).scheme :=
    (schubertInclusion G (w * longestParabolicElement G.rootBase J)).left
  have : Smooth p := SchubertGeometry.partialFlagMorphism_smooth G J
  have : IsReduced (pullback p i) := inferInstance
  have hr : Set.range f = Set.range (pullback.fst p i) :=
    hpre.symm.trans (Scheme.Pullback.range_fst p i).symm
  refine ⟨reducedRangeIso f (pullback.fst p i) hr, ?_⟩
  exact liftPreimmersion_fac (pullback.fst p i) f hr.le

end SchubertGeometry
