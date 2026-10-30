import OrbitComplexity.SchubertGeometry.FlagBundle.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Locally trivial bundles over the flag variety

An associated bundle is a product over every translated unipotent chart.
A proper fibre gives a proper projection to the flag variety.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
namespace SchubertGeometry
universe u

private theorem tensor_fst_pullback {S : Scheme.{u}} {A B Y : Over S} (f : A ⟶ B) :
    IsPullback (fst A Y) (f ⊗ₘ 𝟙 Y) f (fst B Y) := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact lift s.fst (s.snd ≫ snd B Y)
  · intro s
    simp
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simpa using s.condition
    · simp
  · intro s m h1 h2
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h1
    · have he := congrArg (fun t => t ≫ snd B Y) h2
      simpa only [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd] using he

private theorem tensor_range {S : Scheme.{u}} {A B Y : Over S} (f : A ⟶ B)
    [IsOpenImmersion f.left] :
    (f ⊗ₘ 𝟙 Y).left.opensRange = (fst B Y).left ⁻¹ᵁ f.left.opensRange := by
  have hp : IsPullback (fst A Y).left (f ⊗ₘ 𝟙 Y).left f.left (fst B Y).left :=
    (tensor_fst_pullback f).map (Over.forget S)
  have he := Scheme.Hom.opensRange_comp_of_isIso hp.isoPullback.hom
    (pullback.snd f.left (fst B Y).left)
  apply TopologicalSpace.Opens.ext
  change Set.range (f ⊗ₘ 𝟙 Y).left = _
  rw [← hp.isoPullback_hom_snd]
  exact congrArg (fun V : (B ⊗ Y).left.Opens => (V : Set (B ⊗ Y).left))
    (he.trans (Scheme.Hom.opensRange_pullbackSnd f.left (fst B Y).left))

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)
  (Y : GroupActions.Variety K) [ModObj (GroupActions.borelVariety G).toOver Y.toOver]

private theorem chart_overlap (g h : G.points) :
    flagOverlapInclusion G g h ≫ flagChartMorphism G g =
      flagTransition G g h ≫ flagOverlapInclusion G h g ≫ flagChartMorphism G h := by
  apply Over.OverMorphism.ext
  exact ((flagGlueData G).glue_condition g h).symm

private theorem product_base_condition (g h : G.points) :
    flagBundleInclusion G Y g h ≫
        fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫ flagChartMorphism G g =
      flagBundleTransition G Y g h ≫ flagBundleInclusion G Y h g ≫
        fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫ flagChartMorphism G h := by
  simp only [flagBundleInclusion, tensorHom_fst_assoc]
  have he := congrArg (fun f => f ≫ flagOverlapInclusion G h g ≫ flagChartMorphism G h)
    (flagBundleTransition_fst G Y g h)
  simp only [Category.assoc] at he
  rw [he]
  exact congrArg (fun f => fst (flagOverlapVariety G g h).toOver Y.toOver ≫ f)
    (chart_overlap G g h)

/-- The bundle scheme associated with a variety and its Borel action. -/
def flagBundleScheme : Scheme := (flagBundleGlueData G Y).glued

/-- A local product chart of the associated bundle. -/
def flagBundleChart (g : G.points) :
    ((GroupActions.oppositeUnipotentVariety G).toOver ⊗ Y.toOver).left ⟶ flagBundleScheme G Y :=
  (flagBundleGlueData G Y).ι g

/-- Local product charts are open immersions. -/
instance flagBundleChart_isOpen (g : G.points) : IsOpenImmersion (flagBundleChart G Y g) :=
  (flagBundleGlueData G Y).ι_isOpenImmersion g

private theorem base_condition (gh : G.points × G.points) :
    (flagBundleGlueData G Y).toGlueData.diagram.fst gh ≫
        (fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫
          flagChartMorphism G gh.1).left =
      (flagBundleGlueData G Y).toGlueData.diagram.snd gh ≫
        (fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫
          flagChartMorphism G gh.2).left :=
  congrArg Over.Hom.left (product_base_condition G Y gh.1 gh.2)

/-- The projection of the associated bundle to the flag variety. -/
def flagBundleProjection : flagBundleScheme G Y ⟶ (flagVariety G).scheme :=
  Multicoequalizer.desc (flagBundleGlueData G Y).toGlueData.diagram _
    (fun g => (fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫
      flagChartMorphism G g).left) (base_condition G Y)

/-- A product chart preserves the projection to its base. -/
theorem flagBundleChart_projection (g : G.points) :
    flagBundleChart G Y g ≫ flagBundleProjection G Y =
      (fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫
        flagChartMorphism G g).left := by
  unfold flagBundleChart flagBundleProjection
  exact Multicoequalizer.π_desc (flagBundleGlueData G Y).toGlueData.diagram _
    (fun g => (fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver ≫
      flagChartMorphism G g).left) (base_condition G Y) g

/-- The preimage of a flag chart is its bundle chart. -/
theorem flagBundleProjection_preimage (g : G.points) :
    flagBundleProjection G Y ⁻¹ᵁ (flagChartMorphism G g).left.opensRange =
      (flagBundleChart G Y g).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨h, z, rfl⟩ := (flagBundleGlueData G Y).ι_jointly_surjective x
    change G.points at h
    have he := congrArg (fun f => f z) (flagBundleChart_projection G Y h)
    simp only [Over.comp_left] at he
    have hb : (flagSchemeChart G h)
        ((fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver).left z) =
        flagSchemeChart G g u := he.symm.trans hu.symm
    obtain ⟨v, hv, _⟩ := ((flagGlueData G).ι_eq_iff h g _ u).mp hb
    have hz : z ∈ Set.range (flagBundleInclusion G Y h g).left := by
      change z ∈ (flagBundleInclusion G Y h g).left.opensRange
      rw [tensor_range (flagOverlapInclusion G h g)]
      exact ⟨v, hv⟩
    obtain ⟨w, hw⟩ := hz
    refine ⟨((flagBundleTransition G Y h g).left ≫
      (flagBundleInclusion G Y g h).left) w, ?_⟩
    have ht := congrArg (fun f => f w) ((flagBundleGlueData G Y).glue_condition h g)
    change ((flagBundleTransition G Y h g).left ≫
        (flagBundleInclusion G Y g h).left ≫ flagBundleChart G Y g) w =
      ((flagBundleInclusion G Y h g).left ≫ flagBundleChart G Y h) w at ht
    change (flagBundleChart G Y g)
        ((flagBundleInclusion G Y g h).left ((flagBundleTransition G Y h g).left w)) =
      (flagBundleChart G Y h) ((flagBundleInclusion G Y h g).left w) at ht
    rw [hw] at ht
    exact ht
  · rintro ⟨z, rfl⟩
    refine ⟨(fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver).left z, ?_⟩
    have he := congrArg (fun f => f z) (flagBundleChart_projection G Y g)
    simpa only [Scheme.Hom.comp_apply, Over.comp_left] using he.symm

/-- Each bundle chart is the product over its corresponding flag chart. -/
theorem flagBundlePullback (g : G.points) :
    IsPullback (fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver).left
      (flagBundleChart G Y g) (flagChartMorphism G g).left (flagBundleProjection G Y) := by
  exact IsOpenImmersion.isPullback _ _ _ _ (flagBundleChart_projection G Y g)
    (flagBundleProjection_preimage G Y g)

/-- A proper fibre gives a proper projection for the associated bundle. -/
instance flagBundleProjection_isProper [IsProper Y.toSpec] :
    IsProper (flagBundleProjection G Y) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper) (flagSchemeCover G)
  intro g
  change G.points at g
  change IsProper (pullback.snd (flagBundleProjection G Y) (flagChartMorphism G g).left)
  have : IsProper (fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver).left := by
    change IsProper (pullback.fst (GroupActions.oppositeUnipotentVariety G).toSpec Y.toSpec)
    infer_instance
  rw [← (flagBundlePullback G Y g).flip.isoPullback_inv_snd]
  infer_instance

end SchubertGeometry
