import OrbitComplexity.SchubertGeometry.LineBundles.Modules.BundleSections
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.OverlapParameters
import OrbitComplexity.SchubertGeometry.Normality.Models.RankoneTorsorFactors

/-! # The associated-character charts on the simple-root curve -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem negative_section (i : G.rootBase.support) :
    simpleNegativeOppositeFactor G i ≫ flagChartMap G 1 = simpleNegativeSection G i := by
  have hc : flagChartMap G 1 = oppositeUnipotentInclusion G := by
    apply Variety.mapPoints_injective
    funext p
    rw [flagChartMap_points, oppositeUnipotentInclusion_points, one_mul]
  rw [hc, simpleNegativeOppositeFactor_fac]

private theorem positive_section (i : G.rootBase.support) :
    simplePositiveOppositeFactor G i ≫ flagChartMap G ((G.reflectionPoint i.val)⁻¹) =
      simplePositiveSection G i := by
  change simplePositiveOppositeFactor G i ≫ oppositeUnipotentInclusion G ≫
    (leftTranslation (reductiveVariety G)
      (reductivePointsMulEquiv G ((G.reflectionPoint i.val)⁻¹))).hom = _
  exact (simplePositiveSection_opposite G i).symm

private theorem section_change (i : G.rootBase.support) :
    (multiplicativeParameter (K := K) 1 ≫ simplePositiveOppositeFactor G i) ≫
        flagChartMap G ((G.reflectionPoint i.val)⁻¹) =
      ((multiplicativeParameter (K := K) (-1) ≫ simpleNegativeOppositeFactor G i) ≫
        flagChartMap G 1) * (simpleOverlapMorphism G i ≫ borelInclusion G) := by
  simpa only [Category.assoc, positive_section, negative_section] using
    simpleFrames_transition G i

/-- associated-line charts change the fibre by the inverse of the same Borel character. -/
theorem simpleCharacterBundle_transition (i : G.rootBase.support) (chi : G.characters) :
    letI := characterLineAction G chi
    (((multiplicativeParameter (K := K) 1 ≫ simplePositiveOppositeFactor G i) ⊗ₘ
        𝟙 (additiveVariety K).toOver).left) ≫
      flagBundleChart G (additiveVariety K) ((G.reflectionPoint i.val)⁻¹) =
    (lift (fst (affineVariety K (MonoidAlgebra K (Multiplicative ℤ))).toOver
          (additiveVariety K).toOver ≫ multiplicativeParameter (K := K) (-1) ≫
            simpleNegativeOppositeFactor G i)
      ((fst (affineVariety K (MonoidAlgebra K (Multiplicative ℤ))).toOver
          (additiveVariety K).toOver ≫ simpleOverlapMorphism G i) •
            snd (affineVariety K (MonoidAlgebra K (Multiplicative ℤ))).toOver
              (additiveVariety K).toOver)).left ≫
      flagBundleChart G (additiveVariety K) 1 := by
  let := characterLineAction G chi
  simpa only [Category.assoc] using
    sectionBundle_change G (affineVariety K (MonoidAlgebra K (Multiplicative ℤ)))
      (additiveVariety K) ((G.reflectionPoint i.val)⁻¹) 1
      (multiplicativeParameter (K := K) 1 ≫ simplePositiveOppositeFactor G i)
      (multiplicativeParameter (K := K) (-1) ≫ simpleNegativeOppositeFactor G i)
      (simpleOverlapMorphism G i) (section_change G i)

end SchubertGeometry.ProjectiveLine
