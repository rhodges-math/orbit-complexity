import OrbitComplexity.SchubertGeometry.Cells.RichardsonChartPoints
import OrbitComplexity.SchubertGeometry.FlagVariety.BigCellCover
import OrbitComplexity.GroupActions.Actions.RightTranslations
import OrbitComplexity.GroupActions.Varieties.PointImageIso

/-! # Preirreducibility of open Richardson strata

The big-cell inverse produces a regular Richardson chart from an open subset of the Borel.
Its rational image is the open Richardson stratum, so constructibility and reduced induced
structures give the same scheme image.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace ReductiveGroups GroupActions
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private def borelTranslate (u v : G.weylGroup) :
    (borelVariety G).toOver ⟶ (reductiveVariety G).toOver :=
  borelInclusion G ≫
    (leftTranslation (reductiveVariety G) (reductivePointsMulEquiv G (G.weylPoint u))).hom ≫
      (rightTranslation (reductiveVariety G)
        (reductivePointsMulEquiv G (G.weylPoint v)⁻¹)).hom

private theorem borelTranslate_points (u v : G.weylGroup) (a : (borelVariety G).points) :
    Variety.mapPoints (borelTranslate G u v) a =
      reductivePointsMulEquiv G
        (G.weylPoint u * (borelPointsMulEquiv G a : G.points) * (G.weylPoint v)⁻¹) := by
  have hc := Variety.mapPoints_comp (X := borelVariety G)
    (Y := reductiveVariety G) (Z := reductiveVariety G) (borelInclusion G)
    ((leftTranslation (reductiveVariety G)
      (reductivePointsMulEquiv G (G.weylPoint u))).hom ≫
      (rightTranslation (reductiveVariety G)
        (reductivePointsMulEquiv G (G.weylPoint v)⁻¹)).hom) a
  change Variety.mapPoints (_ ≫ _) a = _
  rw [hc, Variety.mapPoints_comp, rightTranslation_points, leftTranslation_points,
    borelInclusion_points]
  calc
    _ = reductivePointsMulEquiv G
        (G.weylPoint u * (borelPointsMulEquiv G a : G.points)) *
          reductivePointsMulEquiv G (G.weylPoint v)⁻¹ :=
      congrArg (fun t : (reductiveVariety G).points =>
        t * reductivePointsMulEquiv G (G.weylPoint v)⁻¹)
        ((reductivePointsMulEquiv G).map_mul (G.weylPoint u)
          (borelPointsMulEquiv G a : G.points)).symm
    _ = _ := ((reductivePointsMulEquiv G).map_mul
      (G.weylPoint u * (borelPointsMulEquiv G a : G.points)) (G.weylPoint v)⁻¹).symm

private def chartOpen (u v : G.weylGroup) : (borelVariety G).scheme.Opens :=
  (borelTranslate G u v).left ⁻¹ᵁ (bigCellMorphism G).left.opensRange

private def chartSource (u v : G.weylGroup) : Variety K :=
  (borelVariety G).openSubvariety (chartOpen G u v)

private def chartInclusion (u v : G.weylGroup) :
    (chartSource G u v).toOver ⟶ (borelVariety G).toOver :=
  (borelVariety G).openInclusion (chartOpen G u v)

private theorem chart_range (u v : G.weylGroup) (a : (chartSource G u v).points) :
    Variety.mapPoints (chartInclusion G u v ≫ borelTranslate G u v) a ∈
      Set.range (Variety.mapPoints (bigCellMorphism G)) := by
  apply Variety.exists_mapPoints_eq (bigCellMorphism G)
  have ha : Variety.mapPoints (chartInclusion G u v) a ∈
      Set.range (Variety.mapPoints (chartInclusion G u v)) := ⟨a, rfl⟩
  rw [Variety.range_mapPoints] at ha
  change (borelVariety G).pointMap (Variety.mapPoints (chartInclusion G u v) a) ∈
    Set.range ((borelVariety G).openInclusion (chartOpen G u v)).left at ha
  rw [Variety.openInclusion_range] at ha
  change (borelTranslate G u v).left
    ((borelVariety G).pointMap (Variety.mapPoints (chartInclusion G u v) a)) ∈
      (bigCellMorphism G).left.opensRange at ha
  rw [Variety.mapPoints_comp, Variety.pointMap_mapPoints]
  exact ha

private def chartLift (u v : G.weylGroup) :
    (chartSource G u v).toOver ⟶ (bigCellVariety G).toOver :=
  Variety.liftOpen (chartInclusion G u v ≫ borelTranslate G u v)
    (bigCellMorphism G) (chart_range G u v)

private theorem chartLift_comp (u v : G.weylGroup) :
    chartLift G u v ≫ bigCellMorphism G = chartInclusion G u v ≫ borelTranslate G u v :=
  Variety.liftOpen_comp _ _ (chart_range G u v)

private theorem chartLift_points (u v : G.weylGroup) (a : (chartSource G u v).points) :
    Variety.mapPoints (bigCellMorphism G) (Variety.mapPoints (chartLift G u v) a) =
      Variety.mapPoints (borelTranslate G u v) (Variety.mapPoints (chartInclusion G u v) a) := by
  have hl := Variety.mapPoints_comp (X := chartSource G u v) (Y := bigCellVariety G)
    (Z := reductiveVariety G) (chartLift G u v) (bigCellMorphism G) a
  have hr := Variety.mapPoints_comp (X := chartSource G u v) (Y := borelVariety G)
    (Z := reductiveVariety G) (chartInclusion G u v) (borelTranslate G u v) a
  exact hl.symm.trans ((congrArg (fun f : (chartSource G u v).toOver ⟶
    (reductiveVariety G).toOver => Variety.mapPoints f a) (chartLift_comp G u v)).trans hr)

private def chartFlagMap (u v : G.weylGroup) :
    (chartSource G u v).toOver ⟶ (flagVariety G).toOver :=
  chartLift G u v ≫ bigCellSnd G ≫
    Variety.orbitMorphism (borelVariety G) (flagVariety G) (weylFlagPoint G v)

private theorem chartFlagMap_points (u v : G.weylGroup) (a : (chartSource G u v).points) :
    Variety.mapPoints (chartFlagMap G u v) a =
      (bigCellPointsEquiv G (Variety.mapPoints (chartLift G u v) a)).2 • weylFlagPoint G v := by
  rw [chartFlagMap, Variety.mapPoints_comp, Variety.mapPoints_comp,
    Variety.mapPoints_orbitMorphism, ← bigCellPointsEquiv_snd]

private theorem chart_factor (u v : G.weylGroup) (a : (chartSource G u v).points) :
    (oppositeUnipotentPointsMulEquiv G
      (bigCellPointsEquiv G (Variety.mapPoints (chartLift G u v) a)).1 : G.points) *
      (borelPointsMulEquiv G
        (bigCellPointsEquiv G (Variety.mapPoints (chartLift G u v) a)).2 : G.points) =
    G.weylPoint u * (borelPointsMulEquiv G
      (Variety.mapPoints (chartInclusion G u v) a) : G.points) * (G.weylPoint v)⁻¹ := by
  have h := (bigCellMorphism_points G (Variety.mapPoints (chartLift G u v) a)).symm.trans
    ((chartLift_points G u v a).trans
      (borelTranslate_points G u v (Variety.mapPoints (chartInclusion G u v) a)))
  exact (reductivePointsMulEquiv G).injective h

private theorem opposite_unipotent_mem (w : G.weylGroup) (m : G.points)
    (hm : m ∈ G.oppositeUnipotentPoints) :
    flagVarietyPointsEquiv G (flagProjection G (m * G.weylPoint w)) ∈
      Set.range (Variety.mapPoints (oppositeSchubertCellInclusion G w)) := by
  rw [oppositeSchubertCell_points_range]
  let b := (oppositeBorelPointsMulEquiv G).symm
    ⟨m, G.oppositeUnipotent_le_oppositeBorel hm⟩
  refine MulAction.mem_orbit_iff.mpr ⟨b, ?_⟩
  rw [weylFlagPoint, oppositeBorelFlag_smul]
  have hb : (oppositeBorelPointsMulEquiv G b : G.points) = m :=
    congrArg Subtype.val ((oppositeBorelPointsMulEquiv G).apply_symm_apply _)
  rw [hb, ← flagProjection_smul]

private theorem chartFlagMap_mem (u v : G.weylGroup) (a : (chartSource G u v).points) :
    Variety.mapPoints (chartFlagMap G u v) a ∈
      Set.range (Variety.mapPoints (richardsonCellInclusion G u v)) := by
  let z := Variety.mapPoints (chartLift G u v) a
  let m : G.points := oppositeUnipotentPointsMulEquiv G (bigCellPointsEquiv G z).1
  let b : G.points := borelPointsMulEquiv G (bigCellPointsEquiv G z).2
  let c : G.points := borelPointsMulEquiv G (Variety.mapPoints (chartInclusion G u v) a)
  have hfac : m * b = G.weylPoint u * c * (G.weylPoint v)⁻¹ := chart_factor G u v a
  have he : b * G.weylPoint v = m⁻¹ * G.weylPoint u * c := by
    calc
      _ = m⁻¹ * (m * b) * G.weylPoint v := by group
      _ = m⁻¹ * (G.weylPoint u * c * (G.weylPoint v)⁻¹) * G.weylPoint v :=
        congrArg (fun p : G.points => m⁻¹ * p * G.weylPoint v) hfac
      _ = _ := by group
  have hq : Variety.mapPoints (chartFlagMap G u v) a =
      flagVarietyPointsEquiv G (flagProjection G (b * G.weylPoint v)) := by
    rw [chartFlagMap_points, weylFlagPoint, borelFlag_smul, ← flagProjection_smul]
  have hflag : flagProjection G (b * G.weylPoint v) =
      flagProjection G (m⁻¹ * G.weylPoint u) := by
    rw [he]
    apply (flagProjection_eq_iff G _ _).mpr
    have heq : (m⁻¹ * G.weylPoint u * c)⁻¹ *
        (m⁻¹ * G.weylPoint u) = c⁻¹ := by group
    rw [heq]
    exact G.borelPoints.inv_mem (borelPointsMulEquiv G
        (Variety.mapPoints (chartInclusion G u v) a)).property
  rw [richardsonCell_points_range]
  refine ⟨?_, ?_⟩
  · rw [schubertCell_points_range, chartFlagMap_points]
    exact MulAction.mem_orbit _ _
  · rw [hq, hflag]
    exact opposite_unipotent_mem G u m⁻¹
      (G.oppositeUnipotentPoints.inv_mem (oppositeUnipotentPointsMulEquiv G
        (bigCellPointsEquiv G z).1).property)

private theorem chartFlagMap_surjective (u v : G.weylGroup)
    (x : (richardsonCell G u v).points) :
    ∃ a : (chartSource G u v).points,
      Variety.mapPoints (chartFlagMap G u v) a =
        Variety.mapPoints (richardsonCellInclusion G u v) x := by
  let q := Variety.mapPoints (richardsonCellInclusion G u v) x
  have hq : q ∈ Set.range (Variety.mapPoints (richardsonCellInclusion G u v)) := ⟨x, rfl⟩
  rw [richardsonCell_points_range] at hq
  obtain ⟨m, hm, hmq⟩ := oppositeCell_unipotent_points G u q hq.2
  have ho := hq.1
  rw [schubertCell_points_range] at ho
  obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp ho
  have hbf : flagVarietyPointsEquiv G
      (flagProjection G ((borelPointsMulEquiv G b : G.points) * G.weylPoint v)) = q := by
    rw [flagProjection_smul, ← borelFlag_smul, ← weylFlagPoint]
    exact hb
  let c := (m * G.weylPoint u)⁻¹ *
    ((borelPointsMulEquiv G b : G.points) * G.weylPoint v)
  have hc : c ∈ G.borelPoints :=
    (flagProjection_eq_iff G _ _).mp
      ((flagVarietyPointsEquiv G).injective (hmq.symm.trans hbf.symm))
  let aB := (borelPointsMulEquiv G).symm ⟨c, hc⟩
  have haB : (borelPointsMulEquiv G aB : G.points) = c :=
    congrArg Subtype.val ((borelPointsMulEquiv G).apply_symm_apply _)
  let mU := (oppositeUnipotentPointsMulEquiv G).symm
    ⟨m⁻¹, G.oppositeUnipotentPoints.inv_mem hm⟩
  let z := (bigCellPointsEquiv G).symm (mU, b)
  have hz : bigCellPointsEquiv G z = (mU, b) :=
    (bigCellPointsEquiv G).apply_symm_apply _
  have hmU : (oppositeUnipotentPointsMulEquiv G mU : G.points) = m⁻¹ :=
    congrArg Subtype.val ((oppositeUnipotentPointsMulEquiv G).apply_symm_apply _)
  have he : G.weylPoint u * c * (G.weylPoint v)⁻¹ =
      m⁻¹ * (borelPointsMulEquiv G b : G.points) := by
    dsimp only [c]
    group
  have hψ : Variety.mapPoints (borelTranslate G u v) aB =
      Variety.mapPoints (bigCellMorphism G) z := by
    rw [borelTranslate_points, bigCellMorphism_points, haB, hz, hmU, he]
    rfl
  have haOpen : (borelVariety G).pointMap aB ∈ chartOpen G u v := by
    change (borelTranslate G u v).left ((borelVariety G).pointMap aB) ∈
      (bigCellMorphism G).left.opensRange
    rw [← Variety.pointMap_mapPoints, hψ]
    exact ⟨(bigCellVariety G).pointMap z, Variety.pointMap_mapPoints _ _ |>.symm⟩
  have haRange : (borelVariety G).pointMap aB ∈
      Set.range (chartInclusion G u v).left := by
    change (borelVariety G).pointMap aB ∈
      Set.range ((borelVariety G).openInclusion (chartOpen G u v)).left
    rwa [Variety.openInclusion_range]
  obtain ⟨a, ha⟩ := Variety.exists_mapPoints_eq (chartInclusion G u v) aB haRange
  have hl : Variety.mapPoints (chartLift G u v) a = z := by
    apply (Variety.isEmbedding_mapPoints (bigCellMorphism G)).injective
    exact (chartLift_points G u v a).trans
      ((congrArg (Variety.mapPoints (borelTranslate G u v)) ha).trans hψ)
  refine ⟨a, ?_⟩
  rw [chartFlagMap_points, hl, hz]
  exact hb

private theorem chartFlagMap_range (u v : G.weylGroup) :
    Set.range (Variety.mapPoints (chartFlagMap G u v)) =
      Set.range (Variety.mapPoints (richardsonCellInclusion G u v)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    exact chartFlagMap_mem G u v a
  · rintro _ ⟨x, rfl⟩
    exact chartFlagMap_surjective G u v x

/-- An open Richardson stratum is preirreducible, including when it is empty. -/
instance richardsonCell_preirreducible (u v : G.weylGroup) :
    PreirreducibleSpace (richardsonCell G u v).scheme := by
  let iB : (chartSource G u v).scheme ⟶ (borelVariety G).scheme :=
    ((borelVariety G).openInclusion (chartOpen G u v)).left
  have : IsOpenImmersion iB := by
    change IsOpenImmersion (chartOpen G u v).ι
    infer_instance
  have : PreirreducibleSpace (chartSource G u v).scheme :=
    iB.isOpenEmbedding.preirreducibleSpace
  have hr : IsPreirreducible (Set.range (chartFlagMap G u v).left) := by
    simpa only [Set.image_univ] using
      (show IsPreirreducible (Set.univ : Set (chartSource G u v).scheme) from
        PreirreducibleSpace.isPreirreducible_univ).image
        (chartFlagMap G u v).left (chartFlagMap G u v).left.continuous.continuousOn
  have he := Variety.range_eq_of_mapPoints (chartFlagMap G u v)
    (richardsonCellInclusion G u v) (chartFlagMap_range G u v)
  rw [he] at hr
  let i : (richardsonCell G u v).scheme ⟶ (flagVariety G).scheme :=
    (richardsonCellInclusion G u v).left
  have : PreirreducibleSpace (Set.range i) :=
    isPreirreducible_iff_preirreducibleSpace.mp hr
  exact i.isEmbedding.toHomeomorph.symm.surjective.preirreducibleSpace
    i.isEmbedding.toHomeomorph.symm.continuous

end
end SchubertGeometry
