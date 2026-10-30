import OrbitComplexity.SchubertGeometry.BSDH.Construction
import OrbitComplexity.SchubertGeometry.FlagBundle.Points
import OrbitComplexity.SchubertGeometry.Parabolics.BruhatClosure
import OrbitComplexity.GroupActions.Varieties.OpenCoverPoints
import OrbitComplexity.GroupActions.Varieties.PointImageIso
import OrbitComplexity.GroupActions.Varieties.SmoothProducts

/-! # Ascending simple-Schubert correspondences

An ascending simple-root correspondence multiplies the two relevant Bruhat closures.
The resulting endpoint lies in the Schubert variety of the appended reflection.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj Pointwise
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)
open ReductiveGroups GroupActions Topology

omit [IsAlgClosed K] [CharZero K] in
private theorem closure_product {A B C : Set G.points} (h : A * B ⊆ C)
    {g k : G.points} (hg : g ∈ closure A) (hk : k ∈ closure B) :
    g * k ∈ closure C := by
  have hb (a : G.points) (ha : a ∈ A) : a * k ∈ closure C :=
    map_mem_closure (f := fun b => a * b)
      SeparatelyContinuousMul.continuous_const_mul hk
      (fun b hb => h ⟨a, ha, b, hb, rfl⟩)
  have hh := map_mem_closure (f := fun a => a * k)
    SeparatelyContinuousMul.continuous_mul_const hg hb
  simpa only [closure_closure] using hh

private theorem ascent_closure_product (v : G.weylGroup) (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v i.val))
    {g k : G.points}
    (hg : g ∈ closure (subgroupDoubleCoset G.borelPoints (G.weylPoint v)))
    (hk : k ∈ closure (subgroupDoubleCoset G.borelPoints
      (G.weylPoint (RootPairing.weylGroup.ofIdx G.rootSystem i.val)))) :
    g * k ∈ closure (subgroupDoubleCoset G.borelPoints
      (G.weylPoint (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))) := by
  apply closure_product G _ hg hk
  have hmul := G.isBruhatSystem.doubleCoset_mul_eq_of_isPos v i hi
  simpa only [G.weylPoint_eq] using hmul.le

private theorem groupFlag_mem_closure (v : G.weylGroup) (g : G.points) :
    flagVarietyPointsEquiv G (flagProjection G g) ∈
        Set.range (Variety.mapPoints (schubertInclusion G v)) ↔
      g ∈ closure (subgroupDoubleCoset G.borelPoints (G.weylPoint v)) := by
  rw [schubertVariety_points_cells, bruhat_doubleCoset_closure]
  simp only [Set.mem_iUnion, schubertCell_points_range, mem_schubertOrbit_iff]

private theorem bundle_point_form (Y : Variety K)
    [ModObj (borelVariety G).toOver Y.toOver]
    (j : Y.toOver ⟶ (flagVariety G).toOver)
    [IsModHom (borelVariety G).toOver j]
    (p : Spec (CommRingCat.of K) ⟶ flagBundleScheme G Y)
    (hp : p ≫ flagBundleProjection G Y ≫ (flagVariety G).toSpec = 𝟙 _) :
    ∃ (g : G.points) (y : Y.points),
      p ≫ flagBundleProjection G Y =
        (flagVarietyPointsEquiv G (flagProjection G g)).val ∧
      p ≫ flagBundleMap G Y j =
        (reductivePointsMulEquiv G g • Variety.mapPoints j y).val := by
  let S := (oppositeUnipotentVariety G).toOver ⊗ Y.toOver
  obtain ⟨index, chartLift, hLift⟩ := point_factors_openCover
    (flagBundleGlueData G Y).openCover p
  let g : G.points := index
  let l : Spec (CommRingCat.of K) ⟶ S.left := chartLift
  have hl : l ≫ flagBundleChart G Y g = p := hLift
  have hc : flagBundleChart G Y g ≫
      (flagBundleProjection G Y ≫ (flagVariety G).toSpec) = S.hom := by
    rw [← Category.assoc, flagBundleChart_projection]
    exact (fst (oppositeUnipotentVariety G).toOver Y.toOver ≫ flagChartMorphism G g).w
  have hL : l ≫ S.hom = 𝟙 _ := by
    calc
      l ≫ S.hom = l ≫ (flagBundleChart G Y g ≫
          (flagBundleProjection G Y ≫ (flagVariety G).toSpec)) :=
        congrArg (fun m => l ≫ m) hc.symm
      _ = (l ≫ flagBundleChart G Y g) ≫ flagBundleProjection G Y ≫
          (flagVariety G).toSpec := by simp only [Category.assoc]
      _ = 𝟙 _ := by rw [hl]; exact hp
  let a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ S := Over.homMk l hL
  let u := (oppositeUnipotentVariety G).pointsEquivOverHom.symm (a ≫ fst _ _)
  let y := Y.pointsEquivOverHom.symm (a ≫ snd _ _)
  have hu : (oppositeUnipotentVariety G).pointsEquivOverHom u = a ≫ fst _ _ :=
    (oppositeUnipotentVariety G).pointsEquivOverHom.apply_symm_apply _
  have hy : Y.pointsEquivOverHom y = a ≫ snd _ _ :=
    Y.pointsEquivOverHom.apply_symm_apply _
  have ha : a = lift ((oppositeUnipotentVariety G).pointsEquivOverHom u)
      (Y.pointsEquivOverHom y) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, hu]
    · rw [lift_snd, hy]
  refine ⟨g * (oppositeUnipotentPointsMulEquiv G u : G.points), y, ?_, ?_⟩
  · rw [← hl, Category.assoc, flagBundleChart_projection]
    change l ≫ (fst (oppositeUnipotentVariety G).toOver Y.toOver).left ≫
      (flagChartMorphism G g).left = _
    have huL : u.val = l ≫ (fst (oppositeUnipotentVariety G).toOver Y.toOver).left :=
      congrArg Over.Hom.left hu
    rw [← Category.assoc, ← huL]
    exact congrArg Subtype.val (flagChartMorphism_points G g u)
  · rw [← hl, Category.assoc, flagBundleChart_map]
    change (a ≫ ((fst (oppositeUnipotentVariety G).toOver Y.toOver ≫
      flagChartMap G g) • (snd (oppositeUnipotentVariety G).toOver Y.toOver ≫ j))).left = _
    rw [ha, ModObj.comp_smul, lift_fst_assoc, lift_snd_assoc]
    change ((reductiveVariety G).pointsEquivOverHom
      (Variety.mapPoints (flagChartMap G g) u) •
        (flagVariety G).pointsEquivOverHom (Variety.mapPoints j y)).left = _
    rw [flagChartMap_points]
    exact (congrArg Over.Hom.left (Variety.pointsEquivOverHom_smul
      (reductiveVariety G) (flagVariety G)
      (reductivePointsMulEquiv G (g * (oppositeUnipotentPointsMulEquiv G u : G.points)))
      (Variety.mapPoints j y))).symm

private abbrev stepFibre (i : G.rootBase.support) : Variety K :=
  schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)

private abbrev stepProjection (i : G.rootBase.support) :=
  flagBundleProjection G (stepFibre G i)

private abbrev stepEndpoint (i : G.rootBase.support) :=
  flagBundleMap G (stepFibre G i)
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))

private instance stepProjection_proper (i : G.rootBase.support) :
    IsProper (stepProjection G i) := flagBundleProjection_isProper G (stepFibre G i)

private instance stepProjection_smooth (i : G.rootBase.support) :
    Smooth (stepProjection G i) := flagBundleProjection_smooth G (stepFibre G i)

@[instance_reducible]
private def stepVariety (v : G.weylGroup) (i : G.rootBase.support) : Variety K where
  scheme := pullback (schubertInclusion G v).left (stepProjection G i)
  toSpec := pullback.fst (schubertInclusion G v).left (stepProjection G i) ≫
    (schubertVariety G v).toSpec
  reduced := by
    have : IsReduced (schubertVariety G v).toOver.left := (schubertVariety G v).reduced
    have : IsLocallyNoetherian (schubertVariety G v).toOver.left := by
      change IsLocallyNoetherian (schubertVariety G v).scheme
      infer_instance
    exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
      (pullback.fst (schubertInclusion G v).left (stepProjection G i))

private def stepMorphism (v : G.weylGroup) (i : G.rootBase.support) :
    (stepVariety G v i).toOver ⟶ (flagVariety G).toOver :=
  Over.homMk
    (pullback.snd (schubertInclusion G v).left (stepProjection G i) ≫ stepEndpoint G i) (by
      change (pullback.snd (schubertInclusion G v).left (stepProjection G i) ≫
        stepEndpoint G i) ≫ (flagVariety G).toSpec =
          pullback.fst (schubertInclusion G v).left (stepProjection G i) ≫
            (schubertVariety G v).toSpec
      rw [Category.assoc, flagBundleMap_toSpec, ← Category.assoc,
        ← pullback.condition, Category.assoc]
      exact congrArg (fun f => pullback.fst (schubertInclusion G v).left
        (stepProjection G i) ≫ f) (schubertInclusion G v).w)

set_option maxHeartbeats 400000 in
private theorem step_point_image (v : G.weylGroup) (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v i.val))
    (x : (stepVariety G v i).points) :
    Variety.mapPoints (stepMorphism G v i) x ∈
      Set.range (Variety.mapPoints (schubertInclusion G
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))) := by
  let f := (schubertInclusion G v).left
  let π := stepProjection G i
  let l : Spec (CommRingCat.of K) ⟶ pullback f π := x.val
  have hx : l ≫ pullback.fst f π ≫ (schubertVariety G v).toSpec = 𝟙 _ := x.property
  let p := l ≫ pullback.snd f π
  have hp : p ≫ π ≫ (flagVariety G).toSpec = 𝟙 _ := by
    have h := congrArg (fun t => l ≫ t ≫ (flagVariety G).toSpec)
      (pullback.condition (f := f) (g := π))
    simp only [Category.assoc] at h
    have hf : f ≫ (flagVariety G).toSpec = (schubertVariety G v).toSpec :=
      (schubertInclusion G v).w
    rw [hf] at h
    simpa only [p, Category.assoc] using h.symm.trans hx
  obtain ⟨g, y, hg, he⟩ := bundle_point_form G (stepFibre G i)
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) p hp
  let a : (schubertVariety G v).points :=
    ⟨l ≫ pullback.fst f π, (Category.assoc _ _ _).trans hx⟩
  have hproj : (l ≫ pullback.fst f π) ≫ f = p ≫ π := by
    dsimp only [p]
    simp only [Category.assoc]
    rw [pullback.condition]
  have hgC : g ∈ closure (subgroupDoubleCoset G.borelPoints (G.weylPoint v)) := by
    apply (groupFlag_mem_closure G v g).mp
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact hproj.trans hg
  obtain ⟨q, hq⟩ := (flagVarietyPointsEquiv G).surjective
    (Variety.mapPoints (schubertInclusion G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) y)
  obtain ⟨k, hk⟩ := flagProjection_surjective G q
  have hyk : flagVarietyPointsEquiv G (flagProjection G k) =
      Variety.mapPoints (schubertInclusion G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) y :=
    (congrArg (flagVarietyPointsEquiv G) hk).trans hq
  have hkC : k ∈ closure (subgroupDoubleCoset G.borelPoints
      (G.weylPoint (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) := by
    apply (groupFlag_mem_closure G _ k).mp
    rw [hyk]
    exact ⟨y, rfl⟩
  have hend : Variety.mapPoints (stepMorphism G v i) x =
      flagVarietyPointsEquiv G (flagProjection G (g * k)) := by
    apply Subtype.ext
    change l ≫ pullback.snd f π ≫ stepEndpoint G i = _
    rw [← Category.assoc]
    change p ≫ stepEndpoint G i = _
    rw [he, ← hyk, flagVarietyAction_points]
    rfl
  rw [hend]
  exact (groupFlag_mem_closure G _ (g * k)).mpr
    (ascent_closure_product G v i hi hgC hkC)

set_option maxHeartbeats 400000 in
/-- An ascending simple correspondence over a Schubert variety ends in the next Schubert variety. -/
theorem schubertAscentStep_mem (v : G.weylGroup) (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v i.val))
    (z : flagBundleScheme G
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)))
    (hz : flagBundleProjection G
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) z ∈
        Set.range (schubertInclusion G v).left) :
    flagBundleMap G
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
      (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) z ∈
        Set.range (schubertInclusion G
          (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left := by
  have hR : Set.range (stepMorphism G v i).left ⊆
      Set.range (schubertInclusion G
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left := by
    apply Variety.range_subset_of_mapPoints
    rintro _ ⟨x, rfl⟩
    exact step_point_image G v i hi x
  have hz' : z ∈ Set.range (pullback.snd (schubertInclusion G v).left
      (stepProjection G i)) := by
    rw [Scheme.Pullback.range_snd]
    exact hz
  obtain ⟨p, hp⟩ := hz'
  have h := hR ⟨p, rfl⟩
  change stepEndpoint G i
    ((pullback.snd (schubertInclusion G v).left (stepProjection G i)) p) ∈ _ at h
  rw [hp] at h
  exact h

end SchubertGeometry
