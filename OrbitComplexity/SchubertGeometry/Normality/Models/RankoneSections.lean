import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoGluing
import OrbitComplexity.GroupActions.Actions.RightTranslations

/-! # Regular frames over the simple-root projective charts -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The positive-root frame uses the inverse simple representative. -/
def simplePositiveSection (i : G.rootBase.support) :
    (additiveVariety K).toOver ⟶ (reductiveVariety G).toOver :=
  gaMorphism G (G.simpleRootMap i) ≫
    (rightTranslation (reductiveVariety G)
      (reductivePointsMulEquiv G ((G.reflectionPoint i.val)⁻¹))).hom

/-- The negative-root frame uses the fixed negative simple-root parameter. -/
def simpleNegativeSection (i : G.rootBase.support) :
    (additiveVariety K).toOver ⟶ (reductiveVariety G).toOver :=
  gaMorphism G (G.negativeSimpleRootMap i)

/-- The positive frame projects to the positive simple-root chart. -/
theorem simplePositiveSection_quotient (i : G.rootBase.support) :
    simplePositiveSection G i ≫ flagQuotientMorphism G =
      simplePositiveChart G i ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  apply Variety.mapPoints_injective
  funext p
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective p
  calc
    Variety.mapPoints (simplePositiveSection G i ≫ flagQuotientMorphism G)
        (additivePointsEquiv K t) =
      flagVarietyPointsEquiv G (flagProjection G
        (gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) := by
      simp only [simplePositiveSection, Variety.mapPoints_comp]
      rw [gaMorphism_points, rightTranslation_points]
      have hm : reductivePointsEquiv G (gaParameterPoint (G.simpleRootMap i) t) *
          reductivePointsMulEquiv G ((G.reflectionPoint i.val)⁻¹) =
        reductivePointsEquiv G
          (gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹) :=
        ((reductivePointsMulEquiv G).map_mul _ _).symm
      rw [hm, flagQuotientMorphism_points]
    _ = _ := (simplePositiveChart_points G i t).symm

/-- The negative frame projects to the negative simple-root chart. -/
theorem simpleNegativeSection_quotient (i : G.rootBase.support) :
    simpleNegativeSection G i ≫ flagQuotientMorphism G =
      simpleNegativeChart G i ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) :=
  (simpleNegativeChart_comp G i).symm

/-- The positive frame lies over the first chart of the chosen projective-line isomorphism. -/
theorem simplePositiveSection_chart (i : G.rootBase.support) :
    simplePositiveSection G i ≫ flagQuotientMorphism G =
      projectiveLineChart K ⟨0⟩ ≫ (simpleSchubertIso G i).inv ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  rw [simplePositiveSection_quotient, ← simpleSchubertIso_positive G i]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The negative frame lies over the second chart of the chosen projective-line isomorphism. -/
theorem simpleNegativeSection_chart (i : G.rootBase.support) :
    simpleNegativeSection G i ≫ flagQuotientMorphism G =
      projectiveLineChart K ⟨1⟩ ≫ (simpleSchubertIso G i).inv ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  rw [simpleNegativeSection_quotient, ← simpleSchubertIso_negative G i]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end SchubertGeometry
