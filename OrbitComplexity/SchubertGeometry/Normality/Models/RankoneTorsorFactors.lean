import OrbitComplexity.SchubertGeometry.Normality.Models.RankoneSections
import OrbitComplexity.SchubertGeometry.Deodhar.OppositeRootPoints
import OrbitComplexity.GroupActions.Varieties.PointImageIso
import OrbitComplexity.GroupActions.Actions.Translations

/-! # Opposite-unipotent factors of the simple-root frames -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups TauCeti
universe u
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
    G.reflectionPoint i.val * gaParameterPoint (G.simpleRootMap i) t *
      (G.reflectionPoint i.val)⁻¹ ∈ G.oppositeUnipotentPoints := by
  have htr : G.rootPointTransport (G.reflectionPoint i.val)
      (G.rootSystem.weylGroupToPerm (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) :=
    G.isBruhatSystem.weyl.transport_reflection i.val
  have hi : ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val) i.val) := by
    intro h
    exact (isPos_neg_index_iff G.rootBase i.val).mp h
      (G.rootBase.isPos_of_mem_support i.property)
  exact positiveSimple_conj_opposite G _ _ htr i hi t

private def liftOver {S : Scheme.{u}} {X Y Z : Over S}
    (i : Z ⟶ X) (f : Y ⟶ X) [IsPreimmersion i.left] [IsReduced Y.left]
    (h : Set.range f.left ⊆ Set.range i.left) : Y ⟶ Z :=
  Over.homMk (liftPreimmersion i.left f.left h) (by
    rw [← i.w, ← Category.assoc, liftPreimmersion_fac]
    exact f.w)

private theorem liftOver_fac {S : Scheme.{u}} {X Y Z : Over S}
    (i : Z ⟶ X) (f : Y ⟶ X) [IsPreimmersion i.left] [IsReduced Y.left]
    (h : Set.range f.left ⊆ Set.range i.left) : liftOver i f h ≫ i = f := by
  apply Over.OverMorphism.ext
  exact liftPreimmersion_fac i.left f.left h

private def oppositeFactor
    (f : (additiveVariety K).toOver ⟶ (reductiveVariety G).toOver)
    (h : Set.range (Variety.mapPoints f) ⊆
      Set.range (Variety.mapPoints (oppositeUnipotentInclusion G))) :
    (additiveVariety K).toOver ⟶ (oppositeUnipotentVariety G).toOver := by
  letI : IsReduced (additiveVariety K).toOver.left := (additiveVariety K).reduced
  exact liftOver (oppositeUnipotentInclusion G) f
    (Variety.range_subset_of_mapPoints f (oppositeUnipotentInclusion G) h)

private theorem oppositeFactor_fac
    (f : (additiveVariety K).toOver ⟶ (reductiveVariety G).toOver)
    (h : Set.range (Variety.mapPoints f) ⊆
      Set.range (Variety.mapPoints (oppositeUnipotentInclusion G))) :
    oppositeFactor G f h ≫ oppositeUnipotentInclusion G = f := by
  let : IsReduced (additiveVariety K).toOver.left := (additiveVariety K).reduced
  exact liftOver_fac (oppositeUnipotentInclusion G) f
    (Variety.range_subset_of_mapPoints f (oppositeUnipotentInclusion G) h)

private theorem negative_image (i : G.rootBase.support) :
    Set.range (Variety.mapPoints (simpleNegativeSection G i)) ⊆
      Set.range (Variety.mapPoints (oppositeUnipotentInclusion G)) := by
  rintro _ ⟨p, rfl⟩
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective p
  refine ⟨(oppositeUnipotentPointsMulEquiv G).symm
    ⟨gaParameterPoint (G.negativeSimpleRootMap i) t, negative_mem G i t⟩, ?_⟩
  rw [oppositeUnipotentInclusion_points, MulEquiv.apply_symm_apply]
  exact (gaMorphism_points G (G.negativeSimpleRootMap i) t).symm

private theorem positive_points (i : G.rootBase.support) (t : K) :
    Variety.mapPoints (simplePositiveSection G i ≫
      (leftTranslation (reductiveVariety G)
        (reductivePointsMulEquiv G (G.reflectionPoint i.val))).hom)
        (additivePointsEquiv K t) =
      reductivePointsEquiv G (G.reflectionPoint i.val *
        gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹) := by
  simp only [simplePositiveSection, Variety.mapPoints_comp]
  rw [gaMorphism_points, rightTranslation_points, leftTranslation_points]
  change reductivePointsMulEquiv G (G.reflectionPoint i.val) *
      (reductivePointsMulEquiv G (gaParameterPoint (G.simpleRootMap i) t) *
        reductivePointsMulEquiv G ((G.reflectionPoint i.val)⁻¹)) = _
  rw [← (reductivePointsMulEquiv G).map_mul,
    ← (reductivePointsMulEquiv G).map_mul, mul_assoc]
  rfl

private theorem positive_image (i : G.rootBase.support) :
    Set.range (Variety.mapPoints (simplePositiveSection G i ≫
      (leftTranslation (reductiveVariety G)
        (reductivePointsMulEquiv G (G.reflectionPoint i.val))).hom)) ⊆
      Set.range (Variety.mapPoints (oppositeUnipotentInclusion G)) := by
  rintro _ ⟨p, rfl⟩
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective p
  refine ⟨(oppositeUnipotentPointsMulEquiv G).symm
    ⟨G.reflectionPoint i.val * gaParameterPoint (G.simpleRootMap i) t *
      (G.reflectionPoint i.val)⁻¹, positive_mem G i t⟩, ?_⟩
  rw [oppositeUnipotentInclusion_points, MulEquiv.apply_symm_apply]
  exact (positive_points G i t).symm

/-- The negative frame has a regular factor in the opposite unipotent subgroup. -/
def simpleNegativeOppositeFactor (i : G.rootBase.support) :
    (additiveVariety K).toOver ⟶ (oppositeUnipotentVariety G).toOver :=
  oppositeFactor G (simpleNegativeSection G i) (negative_image G i)

/-- The translated positive frame has a regular factor in the opposite subgroup. -/
def simplePositiveOppositeFactor (i : G.rootBase.support) :
    (additiveVariety K).toOver ⟶ (oppositeUnipotentVariety G).toOver :=
  oppositeFactor G (simplePositiveSection G i ≫
    (leftTranslation (reductiveVariety G)
      (reductivePointsMulEquiv G (G.reflectionPoint i.val))).hom) (positive_image G i)

/-- The negative opposite-subgroup factor recovers the specified negative frame. -/
theorem simpleNegativeOppositeFactor_fac (i : G.rootBase.support) :
    simpleNegativeOppositeFactor G i ≫ oppositeUnipotentInclusion G =
      simpleNegativeSection G i :=
  oppositeFactor_fac G _ _

/-- The positive opposite-subgroup factor recovers the translated positive frame. -/
theorem simplePositiveOppositeFactor_fac (i : G.rootBase.support) :
    simplePositiveOppositeFactor G i ≫ oppositeUnipotentInclusion G =
      simplePositiveSection G i ≫
        (leftTranslation (reductiveVariety G)
          (reductivePointsMulEquiv G (G.reflectionPoint i.val))).hom :=
  oppositeFactor_fac G _ _

/-- Inverse left translation of the opposite factor is the specified positive frame. -/
theorem simplePositiveSection_opposite (i : G.rootBase.support) :
    simplePositiveSection G i =
      simplePositiveOppositeFactor G i ≫ oppositeUnipotentInclusion G ≫
        (leftTranslation (reductiveVariety G)
          (reductivePointsMulEquiv G ((G.reflectionPoint i.val)⁻¹))).hom := by
  have hc : (leftTranslation (reductiveVariety G)
        (reductivePointsMulEquiv G (G.reflectionPoint i.val))).hom ≫
      (leftTranslation (reductiveVariety G)
        (reductivePointsMulEquiv G ((G.reflectionPoint i.val)⁻¹))).hom = 𝟙 _ := by
    apply Variety.mapPoints_injective
    funext p
    simp only [Variety.mapPoints_comp, leftTranslation_points, Variety.mapPoints_id]
    rw [map_inv]
    exact inv_mul_cancel_left _ _
  have h := congrArg (fun f => f ≫ (leftTranslation (reductiveVariety G)
    (reductivePointsMulEquiv G ((G.reflectionPoint i.val)⁻¹))).hom)
      (simplePositiveOppositeFactor_fac G i)
  simpa only [Category.assoc, hc, Category.comp_id] using h.symm

end SchubertGeometry
