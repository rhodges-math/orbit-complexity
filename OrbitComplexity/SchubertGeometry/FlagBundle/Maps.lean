import OrbitComplexity.SchubertGeometry.FlagBundle.Projection
import OrbitComplexity.SchubertGeometry.Cells.Actions

/-! # Endpoint morphisms of associated bundles

A Borel-equivariant morphism into the flag variety glues to an endpoint morphism
from its associated bundle. The group-action chart formulas agree over the base field.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)
  (Y : GroupActions.Variety K) [ModObj (GroupActions.borelVariety G).toOver Y.toOver]
  (j : Y.toOver ⟶ (flagVariety G).toOver)
  [IsModHom (GroupActions.borelVariety G).toOver j]

private theorem restricted_smul {Z : Over (Spec (CommRingCat.of K))}
    (b : Z ⟶ (GroupActions.borelVariety G).toOver)
    (y : Z ⟶ (flagVariety G).toOver) :
    b • y = (b ≫ GroupActions.borelInclusion G) • y := by
  simp only [CategoryTheory.Hom.smul_def]
  change lift b y ≫ ((GroupActions.borelInclusion G ▷ (flagVariety G).toOver) ≫
    ModObj.smul (M := (GroupActions.reductiveVariety G).toOver)) = _
  rw [← Category.assoc, lift_whiskerRight]

private def bundleEndpointChart (g : G.points) :
    (GroupActions.oppositeUnipotentVariety G).toOver ⊗ Y.toOver ⟶
      (flagVariety G).toOver :=
  (fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫ flagChartMap G g) •
    (snd (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫ j)

private theorem bundleEndpoint_condition (g h : G.points) :
    flagBundleInclusion G Y g h ≫ bundleEndpointChart G Y j g =
      flagBundleTransition G Y g h ≫ flagBundleInclusion G Y h g ≫
        bundleEndpointChart G Y j h := by
  have hf : flagBundleTransition G Y g h ≫
        fst (flagOverlapVariety G h g).toOver Y.toOver ≫
          flagOverlapInclusion G h g ≫ flagChartMap G h =
      fst (flagOverlapVariety G g h).toOver Y.toOver ≫
        flagOverlapCoordinate G g h ≫ flagChartMap G h := by
    have he := congrArg (fun f => f ≫ flagOverlapInclusion G h g ≫ flagChartMap G h)
      (flagBundleTransition_fst G Y g h)
    have hc := congrArg (fun f => fst (flagOverlapVariety G g h).toOver Y.toOver ≫
      f ≫ flagChartMap G h) (flagTransition_comp G g h)
    simp only [Category.assoc] at he hc
    exact he.trans hc
  have hy := congrArg (fun f => f ≫ j) (flagBundleTransition_snd G Y g h)
  rw [IsModHom.map_smul, restricted_smul] at hy
  simp only [Category.assoc] at hy
  have hs := congrArg (fun f => fst (flagOverlapVariety G g h).toOver Y.toOver ≫ f)
    (flagTorsor_section G g h)
  simp only [MonObj.comp_mul] at hs
  simp only [bundleEndpointChart, ModObj.comp_smul, flagBundleInclusion,
    tensorHom_fst_assoc, tensorHom_snd_assoc, Category.id_comp]
  rw [hf, hy, hs, mul_smul]

private theorem endpoint_condition (gh : G.points × G.points) :
    (flagBundleGlueData G Y).toGlueData.diagram.fst gh ≫
        (bundleEndpointChart G Y j gh.1).left =
      (flagBundleGlueData G Y).toGlueData.diagram.snd gh ≫
        (bundleEndpointChart G Y j gh.2).left :=
  congrArg Over.Hom.left (bundleEndpoint_condition G Y j gh.1 gh.2)

/-- The endpoint morphism induced by a Borel-equivariant flag morphism. -/
def flagBundleMap : flagBundleScheme G Y ⟶ (flagVariety G).scheme :=
  Multicoequalizer.desc (flagBundleGlueData G Y).toGlueData.diagram _
    (fun g => (bundleEndpointChart G Y j g).left) (endpoint_condition G Y j)

/-- The endpoint in a local product chart is the action of its local section. -/
theorem flagBundleChart_map (g : G.points) :
    flagBundleChart G Y g ≫ flagBundleMap G Y j =
      ((fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫
        flagChartMap G g) •
        (snd (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫ j)).left := by
  unfold flagBundleChart flagBundleMap
  exact Multicoequalizer.π_desc (flagBundleGlueData G Y).toGlueData.diagram _
    (fun g => (bundleEndpointChart G Y j g).left) (endpoint_condition G Y j) g

/-- The endpoint and base projection agree over the coefficient field. -/
theorem flagBundleMap_toSpec :
    flagBundleMap G Y j ≫ (flagVariety G).toSpec =
      flagBundleProjection G Y ≫ (flagVariety G).toSpec := by
  apply (flagBundleGlueData G Y).openCover.hom_ext
  intro g
  change G.points at g
  change flagBundleChart G Y g ≫ _ = flagBundleChart G Y g ≫ _
  rw [← Category.assoc, flagBundleChart_map, ← Category.assoc,
    flagBundleChart_projection]
  exact (bundleEndpointChart G Y j g).w.trans
    (fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫
      flagChartMorphism G g).w.symm

end SchubertGeometry
