import OrbitComplexity.SchubertGeometry.LineBundles.Characters.TorsorBasechange
import OrbitComplexity.SchubertGeometry.Normality.Models.RankoneTorsorFactors

/-! # Product trivializations of the rank-one Borel torsors -/

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

private theorem negative_base (i : G.rootBase.support) :
    simpleNegativeOppositeFactor G i ≫ flagChartMorphism G 1 =
      simpleNegativeChart G i ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  rw [← flagChartMap_quotient G 1, ← Category.assoc, negative_section,
    simpleNegativeSection_quotient]

private theorem positive_base (i : G.rootBase.support) :
    simplePositiveOppositeFactor G i ≫ flagChartMorphism G ((G.reflectionPoint i.val)⁻¹) =
      simplePositiveChart G i ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  rw [← flagChartMap_quotient, ← Category.assoc, positive_section,
    simplePositiveSection_quotient]

/-- The negative simple-root chart pulls back the flag quotient to affine line times Borel. -/
def simpleNegativeTorsorIso (i : G.rootBase.support) :
    (additiveVariety K).toOver ⊗ (borelVariety G).toOver ≅
      pullback (simpleNegativeChart G i ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
          (flagQuotientMorphism G) :=
  sectionTorsorIso G (additiveVariety K).toOver (simpleNegativeOppositeFactor G i) 1 ≪≫
    pullback.congrHom (negative_base G i) rfl

/-- The positive simple-root chart has the product torsor given by its fixed representative. -/
def simplePositiveTorsorIso (i : G.rootBase.support) :
    (additiveVariety K).toOver ⊗ (borelVariety G).toOver ≅
      pullback (simplePositiveChart G i ≫
        schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
          (flagQuotientMorphism G) :=
  sectionTorsorIso G (additiveVariety K).toOver (simplePositiveOppositeFactor G i)
    ((G.reflectionPoint i.val)⁻¹) ≪≫ pullback.congrHom (positive_base G i) rfl

/-- The negative torsor chart preserves its affine base parameter. -/
theorem simpleNegativeTorsorIso_fst (i : G.rootBase.support) :
    (simpleNegativeTorsorIso G i).hom ≫ pullback.fst _ _ =
      fst (additiveVariety K).toOver (borelVariety G).toOver := by
  simp only [simpleNegativeTorsorIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id, sectionTorsorIso_fst]

/-- The positive torsor chart preserves its affine base parameter. -/
theorem simplePositiveTorsorIso_fst (i : G.rootBase.support) :
    (simplePositiveTorsorIso G i).hom ≫ pullback.fst _ _ =
      fst (additiveVariety K).toOver (borelVariety G).toOver := by
  simp only [simplePositiveTorsorIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id, sectionTorsorIso_fst]

/-- The negative product chart maps to its specified negative section times the Borel factor. -/
theorem simpleNegativeTorsorIso_group (i : G.rootBase.support) :
    (simpleNegativeTorsorIso G i).hom ≫ pullback.snd _ _ =
      (fst (additiveVariety K).toOver (borelVariety G).toOver ≫ simpleNegativeSection G i) *
        (snd (additiveVariety K).toOver (borelVariety G).toOver ≫ borelInclusion G) := by
  simp only [simpleNegativeTorsorIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id,
    sectionTorsorIso_group]
  rw [negative_section]

/-- The positive product chart uses the specified inverse representative and Borel factor. -/
theorem simplePositiveTorsorIso_group (i : G.rootBase.support) :
    (simplePositiveTorsorIso G i).hom ≫ pullback.snd _ _ =
      (fst (additiveVariety K).toOver (borelVariety G).toOver ≫ simplePositiveSection G i) *
        (snd (additiveVariety K).toOver (borelVariety G).toOver ≫ borelInclusion G) := by
  simp only [simplePositiveTorsorIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id,
    sectionTorsorIso_group]
  rw [positive_section]

end SchubertGeometry.ProjectiveLine
