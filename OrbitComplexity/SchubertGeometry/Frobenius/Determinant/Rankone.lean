import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Word
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Endpoint
import OrbitComplexity.SchubertGeometry.LineBundles.Characters.AssociatedPullbacks
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.PolynomialBridge

/-! # The word character section in the fixed rank-one frames -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
universe u

namespace SchubertGeometry.ProjectiveLine

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

private theorem section_frame (N : ℕ) (X : Over (Spec (CommRingCat.of K)))
    (a : X ⟶ (oppositeUnipotentVariety G).toOver) (g : G.points) :
    letI := characterLineAction G (G.positiveRootCharacter ^ N)
    (a ≫ flagChartMorphism G g).left ≫ determinantFlagSection G N =
      (lift a (a ≫ flagChartMap G g ≫
        DeterminantSection.positiveDetPowerMorphism G N)).left ≫
          flagBundleChart G (additiveVariety K) g := by
  let := characterLineAction G (G.positiveRootCharacter ^ N)
  rw [Over.comp_left, Category.assoc, determinantFlagSection_chart]
  have hg : a ≫ lift (𝟙 (oppositeUnipotentVariety G).toOver)
      (flagChartMap G g ≫ DeterminantSection.positiveDetPowerMorphism G N) =
      lift a (a ≫ flagChartMap G g ≫
        DeterminantSection.positiveDetPowerMorphism G N) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  change a.left ≫ ((lift (𝟙 (oppositeUnipotentVariety G).toOver)
      (flagChartMap G g ≫ DeterminantSection.positiveDetPowerMorphism G N)).left ≫
      flagBundleChart G (additiveVariety K) g) = _
  rw [← Category.assoc, ← Over.comp_left, hg]

/-- The positive frame evaluates the original coefficient in the associated section. -/
theorem determinantFlagSection_positive (N : ℕ) (i : G.rootBase.support) :
    letI := characterLineAction G (G.positiveRootCharacter ^ N)
    (simplePositiveSection G i ≫ flagQuotientMorphism G).left ≫
        determinantFlagSection G N =
      (lift (simplePositiveOppositeFactor G i)
        (simplePositiveSection G i ≫ DeterminantSection.positiveDetPowerMorphism G N)).left ≫
          flagBundleChart G (additiveVariety K) ((G.reflectionPoint i.val)⁻¹) := by
  let := characterLineAction G (G.positiveRootCharacter ^ N)
  have hb : simplePositiveOppositeFactor G i ≫
      flagChartMorphism G ((G.reflectionPoint i.val)⁻¹) =
      simplePositiveSection G i ≫ flagQuotientMorphism G := by
    rw [← flagChartMap_quotient, ← Category.assoc, positive_section]
  have hf := section_frame G N (additiveVariety K).toOver
    (simplePositiveOppositeFactor G i) ((G.reflectionPoint i.val)⁻¹)
  rw [hb] at hf
  have hy : simplePositiveOppositeFactor G i ≫
      flagChartMap G ((G.reflectionPoint i.val)⁻¹) ≫
        DeterminantSection.positiveDetPowerMorphism G N =
      simplePositiveSection G i ≫ DeterminantSection.positiveDetPowerMorphism G N := by
    rw [← Category.assoc, positive_section]
  rwa [hy] at hf

/-- The negative frame evaluates the same coefficient in the associated section. -/
theorem determinantFlagSection_negative (N : ℕ) (i : G.rootBase.support) :
    letI := characterLineAction G (G.positiveRootCharacter ^ N)
    (simpleNegativeSection G i ≫ flagQuotientMorphism G).left ≫
        determinantFlagSection G N =
      (lift (simpleNegativeOppositeFactor G i)
        (simpleNegativeSection G i ≫ DeterminantSection.positiveDetPowerMorphism G N)).left ≫
          flagBundleChart G (additiveVariety K) 1 := by
  let := characterLineAction G (G.positiveRootCharacter ^ N)
  have hb : simpleNegativeOppositeFactor G i ≫ flagChartMorphism G 1 =
      simpleNegativeSection G i ≫ flagQuotientMorphism G := by
    rw [← flagChartMap_quotient, ← Category.assoc, negative_section]
  have hf := section_frame G N (additiveVariety K).toOver
    (simpleNegativeOppositeFactor G i) 1
  rw [hb] at hf
  have hy : simpleNegativeOppositeFactor G i ≫ flagChartMap G 1 ≫
      DeterminantSection.positiveDetPowerMorphism G N =
      simpleNegativeSection G i ≫ DeterminantSection.positiveDetPowerMorphism G N := by
    rw [← Category.assoc, negative_section]
  rwa [hy] at hf

/-- The positive comparison uses polynomial chart zero with the original parameter. -/
theorem determinantFlagSection_positive_chart (N : ℕ) (i : G.rootBase.support) :
    letI := characterLineAction G (G.positiveRootCharacter ^ N)
    Spec.map (CommRingCat.ofHom (gaPolynomialEquiv K).symm.toRingHom) ≫
        projectiveLinePolynomialChart K ⟨0⟩ ≫
          ((simpleSchubertIso G i).inv ≫
            schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left ≫
        determinantFlagSection G N =
      (lift (simplePositiveOppositeFactor G i)
        (simplePositiveSection G i ≫ DeterminantSection.positiveDetPowerMorphism G N)).left ≫
          flagBundleChart G (additiveVariety K) ((G.reflectionPoint i.val)⁻¹) := by
  let := characterLineAction G (G.positiveRootCharacter ^ N)
  have h := congrArg (fun q : Spec (CommRingCat.of (SymmetricAlgebra K K)) ⟶
      (flagVariety G).scheme =>
    q ≫ determinantFlagSection G N) (simplePositiveSection_polynomial G i)
  let s := Spec.map (CommRingCat.ofHom (gaPolynomialEquiv K).symm.toRingHom)
  let j := projectiveLinePolynomialChart K ⟨0⟩
  let q := ((simpleSchubertIso G i).inv ≫
    schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left
  let t := determinantFlagSection G N
  have ha : s ≫ j ≫ q ≫ t = (s ≫ (j ≫ q)) ≫ t :=
    (congrArg (fun r : Spec (CommRingCat.of (Polynomial K)) ⟶ determinantLineScheme G N =>
      s ≫ r) (Category.assoc j q t)).symm.trans
        (Category.assoc s (j ≫ q) t).symm
  exact ha.trans (h.symm.trans (determinantFlagSection_positive G N i))

/-- The negative comparison uses polynomial chart one with the original parameter. -/
theorem determinantFlagSection_negative_chart (N : ℕ) (i : G.rootBase.support) :
    letI := characterLineAction G (G.positiveRootCharacter ^ N)
    Spec.map (CommRingCat.ofHom (gaPolynomialEquiv K).symm.toRingHom) ≫
        projectiveLinePolynomialChart K ⟨1⟩ ≫
          ((simpleSchubertIso G i).inv ≫
            schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left ≫
        determinantFlagSection G N =
      (lift (simpleNegativeOppositeFactor G i)
        (simpleNegativeSection G i ≫ DeterminantSection.positiveDetPowerMorphism G N)).left ≫
          flagBundleChart G (additiveVariety K) 1 := by
  let := characterLineAction G (G.positiveRootCharacter ^ N)
  have h := congrArg (fun q : Spec (CommRingCat.of (SymmetricAlgebra K K)) ⟶
      (flagVariety G).scheme =>
    q ≫ determinantFlagSection G N) (simpleNegativeSection_polynomial G i)
  let s := Spec.map (CommRingCat.ofHom (gaPolynomialEquiv K).symm.toRingHom)
  let j := projectiveLinePolynomialChart K ⟨1⟩
  let q := ((simpleSchubertIso G i).inv ≫
    schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left
  let t := determinantFlagSection G N
  have ha : s ≫ j ≫ q ≫ t = (s ≫ (j ≫ q)) ≫ t :=
    (congrArg (fun r : Spec (CommRingCat.of (Polynomial K)) ⟶ determinantLineScheme G N =>
      s ≫ r) (Category.assoc j q t)).symm.trans
        (Category.assoc s (j ≫ q) t).symm
  exact ha.trans (h.symm.trans (determinantFlagSection_negative G N i))

end SchubertGeometry.ProjectiveLine
