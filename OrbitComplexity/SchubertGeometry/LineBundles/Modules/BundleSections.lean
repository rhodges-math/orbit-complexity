import OrbitComplexity.SchubertGeometry.LineBundles.Modules.RegularAction
import OrbitComplexity.SchubertGeometry.FlagBundle.Projection
import OrbitComplexity.GroupActions.Varieties.BorelPoints

/-! # Sections of the flag torsor and their associated-bundle coordinates -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem mapPoints_mul {X H : Variety K} [GrpObj H.toOver]
    (f g : X.toOver ⟶ H.toOver) (x : X.points) :
    Variety.mapPoints (f * g) x = Variety.mapPoints f x * Variety.mapPoints g x := by
  apply H.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_mul]
  change X.pointsEquivOverHom x ≫ (f * g) =
    (X.pointsEquivOverHom x ≫ f) * (X.pointsEquivOverHom x ≫ g)
  exact MonObj.comp_mul _ _ _

private theorem section_flags (X : Variety K) (g h : G.points)
    (f k : X.toOver ⟶ (oppositeUnipotentVariety G).toOver)
    (b : X.toOver ⟶ (borelVariety G).toOver)
    (hs : f ≫ flagChartMap G g = (k ≫ flagChartMap G h) * (b ≫ borelInclusion G))
    (x : X.points) :
    flagChartPoint G g (Variety.mapPoints f x) =
      flagChartPoint G h (Variety.mapPoints k x) := by
  have he := congrArg (fun m => Variety.mapPoints m x) hs
  rw [mapPoints_mul] at he
  simp only [Variety.mapPoints_comp, flagChartMap_points, borelInclusion_points] at he
  let u := oppositeUnipotentPointsMulEquiv G (Variety.mapPoints f x)
  let v := oppositeUnipotentPointsMulEquiv G (Variety.mapPoints k x)
  let c := borelPointsMulEquiv G (Variety.mapPoints b x)
  have hg : g * u = (h * v) * c := by
    apply (reductivePointsMulEquiv G).injective
    change reductivePointsEquiv G (g * u) = reductivePointsMulEquiv G ((h * v) * c)
    rw [(reductivePointsMulEquiv G).map_mul]
    exact he
  change flagProjection G (g * u) = flagProjection G (h * v)
  rw [flagProjection_eq_iff]
  have hc : (g * u)⁻¹ * (h * v) = (c : G.points)⁻¹ := by rw [hg]; group
  rw [hc]
  exact G.borelPoints.inv_mem c.property

/-- A regular change of torsor sections gives the overlap and its exact Borel factor. -/
theorem sectionOverlap_exists (X : Variety K) (g h : G.points)
    (f k : X.toOver ⟶ (oppositeUnipotentVariety G).toOver)
    (b : X.toOver ⟶ (borelVariety G).toOver)
    (hs : f ≫ flagChartMap G g = (k ≫ flagChartMap G h) * (b ≫ borelInclusion G)) :
    ∃ q : X.toOver ⟶ (flagOverlapVariety G g h).toOver,
      q ≫ flagOverlapInclusion G g h = f ∧
      q ≫ flagOverlapCoordinate G g h = k ∧ q ≫ flagOverlapBorel G g h = b := by
  have hr : ∀ x : X.points,
      Variety.mapPoints f x ∈ Set.range (Variety.mapPoints (flagOverlapInclusion G g h)) := by
    intro x
    rw [Variety.range_mapPoints]
    change (oppositeUnipotentVariety G).pointMap (Variety.mapPoints f x) ∈
      Set.range ((oppositeUnipotentVariety G).openInclusion (flagOverlap G g h)).left
    rw [Variety.openInclusion_range]
    exact mem_flagOverlap_of_flag G g h _ _ (section_flags G X g h f k b hs x)
  let q := Variety.liftOpen f (flagOverlapInclusion G g h) hr
  have hq : q ≫ flagOverlapInclusion G g h = f := Variety.liftOpen_comp _ _ _
  have hk : q ≫ flagOverlapCoordinate G g h = k := by
    apply Variety.mapPoints_injective
    funext x
    apply flagChartPoint_injective G h
    rw [Variety.mapPoints_comp, ← flagOverlapCoordinate_flag]
    rw [← Variety.mapPoints_comp, hq]
    exact section_flags G X g h f k b hs x
  have hb : q ≫ flagOverlapBorel G g h = b := by
    have ht := congrArg (fun m => q ≫ m) (flagTorsor_section G g h)
    simp only [MonObj.comp_mul, ← Category.assoc] at ht
    rw [hq, hk] at ht
    have he : (q ≫ flagOverlapBorel G g h) ≫ borelInclusion G = b ≫ borelInclusion G :=
      mul_left_cancel (ht.symm.trans hs)
    have : Mono (borelInclusion G) := Over.mono_of_mono_left _
    exact (cancel_mono (borelInclusion G)).mp he
  exact ⟨q, hq, hk, hb⟩

/-- The associated-bundle charts change the fibre by the same Borel transition. -/
theorem sectionBundle_change (X Y : Variety K)
    [ModObj (borelVariety G).toOver Y.toOver] (g h : G.points)
    (f k : X.toOver ⟶ (oppositeUnipotentVariety G).toOver)
    (b : X.toOver ⟶ (borelVariety G).toOver)
    (hs : f ≫ flagChartMap G g = (k ≫ flagChartMap G h) * (b ≫ borelInclusion G)) :
    (f ⊗ₘ 𝟙 Y.toOver).left ≫ flagBundleChart G Y g =
      (lift (fst X.toOver Y.toOver ≫ k)
        ((fst X.toOver Y.toOver ≫ b) • snd X.toOver Y.toOver)).left ≫
          flagBundleChart G Y h := by
  obtain ⟨q, hq, hk, hb⟩ := sectionOverlap_exists G X g h f k b hs
  have h0 : (q ⊗ₘ 𝟙 Y.toOver) ≫ flagBundleInclusion G Y g h = f ⊗ₘ 𝟙 Y.toOver := by
    change (q ⊗ₘ 𝟙 Y.toOver) ≫ (flagOverlapInclusion G g h ⊗ₘ 𝟙 Y.toOver) = _
    rw [tensorHom_comp_tensorHom, hq, Category.id_comp]
  have h1 : (q ⊗ₘ 𝟙 Y.toOver) ≫ flagBundleTransition G Y g h ≫
      flagBundleInclusion G Y h g =
      lift (fst X.toOver Y.toOver ≫ k)
        ((fst X.toOver Y.toOver ≫ b) • snd X.toOver Y.toOver) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [flagBundleInclusion, Category.assoc, tensorHom_fst, lift_fst]
      rw [← Category.assoc (flagBundleTransition G Y g h), flagBundleTransition_fst]
      simp only [Category.assoc, tensorHom_fst_assoc]
      rw [flagTransition_comp]
      simpa only [Category.assoc] using
        congrArg (fun m => fst X.toOver Y.toOver ≫ m) hk
    · simp only [flagBundleInclusion, Category.assoc, tensorHom_snd,
        Category.comp_id, lift_snd]
      rw [flagBundleTransition_snd, ModObj.comp_smul]
      simp only [tensorHom_fst_assoc, tensorHom_snd, Category.comp_id]
      simpa only [Category.assoc] using congrArg
        (fun m => (fst X.toOver Y.toOver ≫ m) • snd X.toOver Y.toOver) hb
  have ht := congrArg (fun m => (q ⊗ₘ 𝟙 Y.toOver).left ≫ m)
    ((flagBundleGlueData G Y).glue_condition g h)
  change (q ⊗ₘ 𝟙 Y.toOver).left ≫
      (flagBundleTransition G Y g h).left ≫
        (flagBundleInclusion G Y h g).left ≫ flagBundleChart G Y h =
    (q ⊗ₘ 𝟙 Y.toOver).left ≫
      (flagBundleInclusion G Y g h).left ≫ flagBundleChart G Y g at ht
  have he : ((q ⊗ₘ 𝟙 Y.toOver) ≫ flagBundleInclusion G Y g h).left ≫
      flagBundleChart G Y g =
      ((q ⊗ₘ 𝟙 Y.toOver) ≫ flagBundleTransition G Y g h ≫
        flagBundleInclusion G Y h g).left ≫ flagBundleChart G Y h := by
    simpa only [Over.comp_left, Category.assoc] using ht.symm
  rw [h0, h1] at he
  exact he

end SchubertGeometry.ProjectiveLine
