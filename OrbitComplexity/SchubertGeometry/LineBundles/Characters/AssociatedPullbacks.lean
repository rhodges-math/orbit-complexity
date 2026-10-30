import OrbitComplexity.SchubertGeometry.LineBundles.Characters.AssociatedTransition
import OrbitComplexity.SchubertGeometry.LineBundles.Characters.SimpleTorsors

/-! # Cartesian charts of the associated-character bundle -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
universe u

private theorem tensor_fst_pullback {S : Scheme.{u}} {X U Y : Over S} (f : X ⟶ U) :
    IsPullback (fst X Y) (f ⊗ₘ 𝟙 Y) f (fst U Y) := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact lift s.fst (s.snd ≫ snd U Y)
  · intro s
    simp
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simpa using s.condition
    · simp
  · intro s m h1 h2
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h1
    · have he := congrArg (fun t => t ≫ snd U Y) h2
      simpa only [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd] using he

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Every coordinate morphism pulls an associated chart back as its product with the fibre. -/
theorem sectionBundle_pullback (Y : Variety K)
    [ModObj (borelVariety G).toOver Y.toOver]
    (X : Over (Spec (CommRingCat.of K)))
    (f : X ⟶ (oppositeUnipotentVariety G).toOver) (g : G.points) :
    IsPullback (fst X Y.toOver).left
      ((f ⊗ₘ 𝟙 Y.toOver).left ≫ flagBundleChart G Y g)
      (f ≫ flagChartMorphism G g).left (flagBundleProjection G Y) := by
  simpa only [Over.comp_left, Over.forget_obj, Over.forget_map] using
    ((tensor_fst_pullback f).map (Over.forget (Spec (CommRingCat.of K)))).paste_vert
      (flagBundlePullback G Y g)

private theorem negative_base (i : G.rootBase.support) :
    simpleNegativeOppositeFactor G i ≫ flagChartMorphism G 1 =
      simpleNegativeChart G i ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  have hc : flagChartMap G 1 = oppositeUnipotentInclusion G := by
    apply Variety.mapPoints_injective
    funext p
    rw [flagChartMap_points, oppositeUnipotentInclusion_points, one_mul]
  rw [← flagChartMap_quotient, ← Category.assoc, hc,
    simpleNegativeOppositeFactor_fac, simpleNegativeSection_quotient]

private theorem positive_base (i : G.rootBase.support) :
    simplePositiveOppositeFactor G i ≫ flagChartMorphism G ((G.reflectionPoint i.val)⁻¹) =
      simplePositiveChart G i ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  have hc : simplePositiveOppositeFactor G i ≫
      flagChartMap G ((G.reflectionPoint i.val)⁻¹) = simplePositiveSection G i := by
    change simplePositiveOppositeFactor G i ≫ oppositeUnipotentInclusion G ≫
      (leftTranslation (reductiveVariety G)
        (reductivePointsMulEquiv G ((G.reflectionPoint i.val)⁻¹))).hom = _
    exact (simplePositiveSection_opposite G i).symm
  rw [← flagChartMap_quotient, ← Category.assoc, hc, simplePositiveSection_quotient]

/-- The positive chart is the full pullback of the associated-character bundle. -/
theorem simplePositiveBundle_pullback (i : G.rootBase.support) (chi : G.characters) :
    letI := characterLineAction G chi
    IsPullback (fst (additiveVariety K).toOver (additiveVariety K).toOver).left
      ((simplePositiveOppositeFactor G i ⊗ₘ 𝟙 (additiveVariety K).toOver).left ≫
        flagBundleChart G (additiveVariety K) ((G.reflectionPoint i.val)⁻¹))
      (simplePositiveChart G i ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left
      (flagBundleProjection G (additiveVariety K)) := by
  let := characterLineAction G chi
  have h := sectionBundle_pullback G (additiveVariety K) (additiveVariety K).toOver
    (simplePositiveOppositeFactor G i) ((G.reflectionPoint i.val)⁻¹)
  rw [positive_base] at h
  exact h

/-- The negative chart is the full pullback of the associated-character bundle. -/
theorem simpleNegativeBundle_pullback (i : G.rootBase.support) (chi : G.characters) :
    letI := characterLineAction G chi
    IsPullback (fst (additiveVariety K).toOver (additiveVariety K).toOver).left
      ((simpleNegativeOppositeFactor G i ⊗ₘ 𝟙 (additiveVariety K).toOver).left ≫
        flagBundleChart G (additiveVariety K) 1)
      (simpleNegativeChart G i ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left
      (flagBundleProjection G (additiveVariety K)) := by
  let := characterLineAction G chi
  have h := sectionBundle_pullback G (additiveVariety K) (additiveVariety K).toOver
    (simpleNegativeOppositeFactor G i) 1
  rw [negative_base] at h
  exact h

end SchubertGeometry.ProjectiveLine
