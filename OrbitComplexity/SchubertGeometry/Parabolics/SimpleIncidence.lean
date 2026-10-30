import OrbitComplexity.SchubertGeometry.Parabolics.BundleEmbedding
import OrbitComplexity.SchubertGeometry.Parabolics.SimpleFibre
import OrbitComplexity.SchubertGeometry.FlagBundle.Maps
import OrbitComplexity.SchubertGeometry.FlagBundle.Smooth
import OrbitComplexity.SchubertGeometry.FlagBundle.Points
import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoProperties
import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoSmooth
import OrbitComplexity.GroupActions.Varieties.ClosedImage
import OrbitComplexity.GroupActions.Actions.RelativeTwist
import OrbitComplexity.GroupActions.Varieties.ProductImmersions

/-! # Incidence of simple partial flags

The associated bundle of a simple Schubert variety identifies with pairs of
complete flags having the same simple partial flag. The closed correspondence
is surjective on rational points, and its smooth target is reduced.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
universe u

private theorem fibre_constant {S X Y Z : Scheme.{u}} (p : X ⟶ Y)
    (x : X ⟶ S) (y : Y ⟶ S) (z : Z ⟶ S) (hp : p ≫ y = x)
    (b : S ⟶ Y) (hb : b ≫ y = 𝟙 S) (e : Z ≅ pullback p b)
    (j : Z ⟶ X) (he : e.hom ≫ pullback.fst p b = j) (hj : j ≫ x = z) :
    j ≫ p = z ≫ b := by
  have hs : e.hom ≫ pullback.snd p b = z := by
    have h := congrArg (fun f => e.hom ≫ f ≫ y) (pullback.condition (f := p) (g := b))
    simp only [Category.assoc] at h
    rw [hp, hb, Category.comp_id] at h
    exact h.symm.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ x) he).trans hj))
  rw [← he, Category.assoc, pullback.condition, ← Category.assoc, hs]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (i : G.rootBase.support)

private abbrev simpleFibre : Variety K :=
  schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)

private abbrev simpleInclusion : (simpleFibre G i).toOver ⟶ (flagVariety G).toOver :=
  schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)

private theorem simple_constant : simpleInclusion G i ≫ partialFlagMorphism G {i} =
    toUnit (simpleFibre G i).toOver ≫ (flagVariety G).pointsEquivOverHom (baseFlagPoint G) ≫
      partialFlagMorphism G {i} := by
  obtain ⟨e, he⟩ := simpleSchubert_fibre G i
  let p : (flagVariety G).scheme ⟶ (partialFlagVariety G {i}).scheme :=
    (partialFlagMorphism G {i}).left
  let b : Spec (CommRingCat.of K) ⟶ (partialFlagVariety G {i}).scheme :=
    (baseFlagPoint G).val ≫ p
  have hb : b ≫ (partialFlagVariety G {i}).toSpec = 𝟙 _ := by
    have hp : p ≫ (partialFlagVariety G {i}).toSpec = (flagVariety G).toSpec :=
      (partialFlagMorphism G {i}).w
    change ((baseFlagPoint G).val ≫ p) ≫ _ = _
    rw [Category.assoc, hp, (baseFlagPoint G).property]
  apply Over.OverMorphism.ext
  change (simpleInclusion G i).left ≫ p = (simpleFibre G i).toSpec ≫ b
  exact fibre_constant p (flagVariety G).toSpec (partialFlagVariety G {i}).toSpec
    (simpleFibre G i).toSpec (partialFlagMorphism G {i}).w b hb e
    (simpleInclusion G i).left he (simpleInclusion G i).w

private theorem quotient_orbit : flagQuotientMorphism G =
    Variety.orbitMorphism (reductiveVariety G) (flagVariety G) (baseFlagPoint G) := by
  apply Variety.mapPoints_injective
  funext g
  obtain ⟨g, rfl⟩ := (reductivePointsMulEquiv G).surjective g
  change Variety.mapPoints (flagQuotientMorphism G) (reductivePointsEquiv G g) = _
  rw [flagQuotientMorphism_points G g, Variety.mapPoints_orbitMorphism,
    baseFlagPoint, flagVarietyAction_points G g]
  apply congrArg (flagVarietyPointsEquiv G)
  change flagProjection G g = flagProjection G (g * 1)
  rw [mul_one]

private theorem chart_orbit (g : G.points) : flagChartMorphism G g =
    flagChartMap G g • (toUnit (oppositeUnipotentVariety G).toOver ≫
      (flagVariety G).pointsEquivOverHom (baseFlagPoint G)) := by
  rw [← flagChartMap_quotient, quotient_orbit]
  simp only [Variety.orbitMorphism, CategoryTheory.Hom.smul_def, comp_lift_assoc,
    Category.comp_id, comp_toUnit_assoc]

private theorem simple_incidence_condition :
    flagBundleProjection G (simpleFibre G i) ≫ (partialFlagMorphism G {i}).left =
      flagBundleMap G (simpleFibre G i) (simpleInclusion G i) ≫
        (partialFlagMorphism G {i}).left := by
  let : IsModHom (reductiveVariety G).toOver (partialFlagMorphism G {i}) :=
    partialFlagMorphism_isModHom G {i}
  apply (flagBundleGlueData G (simpleFibre G i)).openCover.hom_ext
  intro g
  change G.points at g
  change flagBundleChart G (simpleFibre G i) g ≫ _ =
    flagBundleChart G (simpleFibre G i) g ≫ _
  rw [← Category.assoc, flagBundleChart_projection,
    ← Category.assoc, flagBundleChart_map]
  change ((fst _ _ ≫ flagChartMorphism G g) ≫ partialFlagMorphism G {i}).left =
    (((fst _ _ ≫ flagChartMap G g) • (snd _ _ ≫ simpleInclusion G i)) ≫
      partialFlagMorphism G {i}).left
  apply congrArg Over.Hom.left
  rw [chart_orbit, ModObj.comp_smul, IsModHom.map_smul, IsModHom.map_smul,
    Category.assoc]
  simp only [Category.assoc]
  rw [simple_constant G i]
  simp only [comp_toUnit_assoc]

private def simpleIncidenceMap : flagBundleScheme G (simpleFibre G i) ⟶
    pullback (partialFlagMorphism G {i}).left (partialFlagMorphism G {i}).left :=
  pullback.lift (flagBundleProjection G (simpleFibre G i))
    (flagBundleMap G (simpleFibre G i) (simpleInclusion G i))
    (simple_incidence_condition G i)

private theorem incidence_toSpec :
    pullback.fst (partialFlagMorphism G {i}).left (partialFlagMorphism G {i}).left ≫
        (flagVariety G).toSpec =
      pullback.snd (partialFlagMorphism G {i}).left (partialFlagMorphism G {i}).left ≫
        (flagVariety G).toSpec := by
  let p : (flagVariety G).scheme ⟶ (partialFlagVariety G {i}).scheme :=
    (partialFlagMorphism G {i}).left
  have hp : p ≫ (partialFlagVariety G {i}).toSpec = (flagVariety G).toSpec :=
    (partialFlagMorphism G {i}).w
  calc
    _ = pullback.fst p p ≫ (p ≫ (partialFlagVariety G {i}).toSpec) :=
      congrArg (fun f => pullback.fst p p ≫ f) hp.symm
    _ = pullback.snd p p ≫ (p ≫ (partialFlagVariety G {i}).toSpec) := by
      rw [← Category.assoc, pullback.condition, Category.assoc]
    _ = _ := congrArg (fun f => pullback.snd p p ≫ f) hp

private abbrev incidenceVariety : Variety K where
  scheme := pullback (partialFlagMorphism G {i}).left (partialFlagMorphism G {i}).left
  toSpec := pullback.fst (partialFlagMorphism G {i}).left (partialFlagMorphism G {i}).left ≫
    (flagVariety G).toSpec
  reduced := by
    let p : (flagVariety G).scheme ⟶ (partialFlagVariety G {i}).scheme :=
      (partialFlagMorphism G {i}).left
    change IsReduced (pullback p p)
    have : Smooth p := partialFlagMorphism_smooth G {i}
    have : IsReduced (flagVariety G).scheme := (flagVariety G).reduced
    have : IsLocallyNoetherian (flagVariety G).scheme := inferInstance
    exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.snd p p)

private def incidenceFst : (incidenceVariety G i).toOver ⟶ (flagVariety G).toOver :=
  Over.homMk (pullback.fst (partialFlagMorphism G {i}).left
    (partialFlagMorphism G {i}).left)

private def incidenceSnd : (incidenceVariety G i).toOver ⟶ (flagVariety G).toOver :=
  Over.homMk (pullback.snd (partialFlagMorphism G {i}).left
    (partialFlagMorphism G {i}).left) (incidence_toSpec G i).symm

private def incidencePair : (incidenceVariety G i).toOver ⟶
    (flagVariety G).toOver ⊗ (flagVariety G).toOver :=
  lift (incidenceFst G i) (incidenceSnd G i)

private theorem incidencePair_fst : (incidencePair G i).left ≫
    (fst (flagVariety G).toOver (flagVariety G).toOver).left =
      pullback.fst (partialFlagMorphism G {i}).left (partialFlagMorphism G {i}).left :=
  congrArg Over.Hom.left (lift_fst (incidenceFst G i) (incidenceSnd G i))

private theorem incidencePair_snd : (incidencePair G i).left ≫
    (snd (flagVariety G).toOver (flagVariety G).toOver).left =
      pullback.snd (partialFlagMorphism G {i}).left (partialFlagMorphism G {i}).left :=
  congrArg Over.Hom.left (lift_snd (incidenceFst G i) (incidenceSnd G i))

private theorem incidencePair_isClosed : IsClosedImmersion (incidencePair G i).left := by
  let p : (flagVariety G).scheme ⟶ (partialFlagVariety G {i}).scheme :=
    (partialFlagMorphism G {i}).left
  have hp : p ≫ (partialFlagVariety G {i}).toSpec = (flagVariety G).toSpec :=
    (partialFlagMorphism G {i}).w
  have he : (incidencePair G i).left =
      pullback.mapDesc p p (partialFlagVariety G {i}).toSpec ≫
        (pullback.congrHom hp hp).hom := by
    apply pullback.hom_ext
    · change (incidencePair G i).left ≫
        (fst (flagVariety G).toOver (flagVariety G).toOver).left = _
      rw [incidencePair_fst]
      simp [pullback.congrHom, pullback.map, Category.assoc, p]
    · change (incidencePair G i).left ≫
        (snd (flagVariety G).toOver (flagVariety G).toOver).left = _
      rw [incidencePair_snd]
      simp [pullback.congrHom, pullback.map, Category.assoc, p]
  rw [he]
  have : IsSeparated (partialFlagVariety G {i}).toSpec :=
    (partialFlagVariety G {i}).separated
  have : IsClosedImmersion (pullback.mapDesc p p (partialFlagVariety G {i}).toSpec) :=
    inferInstance
  have : IsIso (pullback.congrHom hp hp).hom := inferInstance
  infer_instance

private theorem simpleIncidenceMap_isClosed : IsClosedImmersion (simpleIncidenceMap G i) := by
  have : IsClosedImmersion (incidencePair G i).left := incidencePair_isClosed G i
  have he : simpleIncidenceMap G i ≫ (incidencePair G i).left =
      pullback.lift (flagBundleProjection G (simpleFibre G i))
        (flagBundleMap G (simpleFibre G i) (simpleInclusion G i))
        (flagBundleMap_toSpec G (simpleFibre G i) (simpleInclusion G i)).symm := by
    apply pullback.hom_ext
    · change (simpleIncidenceMap G i ≫ (incidencePair G i).left) ≫
        (fst (flagVariety G).toOver (flagVariety G).toOver).left = _
      rw [Category.assoc, incidencePair_fst]
      exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
    · change (simpleIncidenceMap G i ≫ (incidencePair G i).left) ≫
        (snd (flagVariety G).toOver (flagVariety G).toOver).left = _
      rw [Category.assoc, incidencePair_snd]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  have : IsClosedImmersion (simpleIncidenceMap G i ≫ (incidencePair G i).left) := by
    rw [he]
    exact flagBundlePair_isClosed G (simpleFibre G i) (simpleInclusion G i)
  exact IsClosedImmersion.of_comp_isClosedImmersion
    (simpleIncidenceMap G i) (incidencePair G i).left

omit [IsAlgClosed K] [CharZero K] in
private theorem point_range (X : Variety K) (p : X.points) :
    Set.range p.val = {X.pointMap p} := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact Set.mem_singleton_iff.mpr (congrArg p.val (Subsingleton.elim _ _))
  · intro hx
    exact ⟨IsLocalRing.closedPoint K, (Set.mem_singleton_iff.mp hx).symm⟩

private theorem simple_point_fibre (q : (flagVariety G).points) :
    q ∈ Set.range (Variety.mapPoints (simpleInclusion G i)) ↔
      Variety.mapPoints (partialFlagMorphism G {i}) q =
        Variety.mapPoints (partialFlagMorphism G {i}) (baseFlagPoint G) := by
  obtain ⟨e, he⟩ := simpleSchubert_fibre G i
  let p : (flagVariety G).scheme ⟶ (partialFlagVariety G {i}).scheme :=
    (partialFlagMorphism G {i}).left
  let b : Spec (CommRingCat.of K) ⟶ (partialFlagVariety G {i}).scheme :=
    (baseFlagPoint G).val ≫ p
  have hr : Set.range (simpleInclusion G i).left = p ⁻¹' Set.range b := by
    rw [← he]
    change Set.range ((pullback.fst p b) ∘ e.hom) = _
    exact (e.hom.homeomorph.surjective.range_comp _).trans (Scheme.Pullback.range_fst p b)
  let y := Variety.mapPoints (partialFlagMorphism G {i}) (baseFlagPoint G)
  have hb : Set.range b = {(partialFlagVariety G {i}).pointMap y} := point_range _ y
  rw [Variety.range_mapPoints (simpleInclusion G i), hr, hb]
  change p ((flagVariety G).pointMap q) = (partialFlagVariety G {i}).pointMap y ↔ _
  rw [← Variety.pointMap_mapPoints,
    (partialFlagVariety G {i}).pointMap_injective.eq_iff]

private theorem incidence_points_equal (q : (incidenceVariety G i).points) :
    Variety.mapPoints (partialFlagMorphism G {i}) (Variety.mapPoints (incidenceFst G i) q) =
      Variety.mapPoints (partialFlagMorphism G {i}) (Variety.mapPoints (incidenceSnd G i) q) := by
  have h : incidenceFst G i ≫ partialFlagMorphism G {i} =
      incidenceSnd G i ≫ partialFlagMorphism G {i} := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  simpa only [Variety.mapPoints_comp] using congrArg (fun f => Variety.mapPoints f q) h

private theorem compatible_preimage (q : (incidenceVariety G i).points) :
    ∃ g : G.points, ∃ y : (simpleFibre G i).points,
      flagVarietyPointsEquiv G (flagProjection G g) =
        Variety.mapPoints (incidenceFst G i) q ∧
      reductivePointsMulEquiv G g • Variety.mapPoints (simpleInclusion G i) y =
        Variety.mapPoints (incidenceSnd G i) q := by
  obtain ⟨a, ha⟩ := (flagVarietyPointsEquiv G).surjective
    (Variety.mapPoints (incidenceFst G i) q)
  obtain ⟨g, rfl⟩ := flagProjection_surjective G a
  obtain ⟨b, hb⟩ := (flagVarietyPointsEquiv G).surjective
    (Variety.mapPoints (incidenceSnd G i) q)
  obtain ⟨h, rfl⟩ := flagProjection_surjective G b
  have hrel : g⁻¹ * h ∈ standardParabolicPoints G {i} := by
    have he := incidence_points_equal G i q
    rw [← ha, ← hb, partialFlagMorphism_points G {i} (flagProjection G g),
      partialFlagMorphism_points G {i} (flagProjection G h),
      (partialFlagPointsEquiv G {i}).injective.eq_iff, partialFlagProjection_eq] at he
    exact he
  have hbase : Variety.mapPoints (partialFlagMorphism G {i})
      (flagVarietyPointsEquiv G (flagProjection G (g⁻¹ * h))) =
        Variety.mapPoints (partialFlagMorphism G {i}) (baseFlagPoint G) := by
    change Variety.mapPoints (partialFlagMorphism G {i})
        (flagVarietyPointsEquiv G (flagProjection G (g⁻¹ * h))) =
      Variety.mapPoints (partialFlagMorphism G {i})
        (flagVarietyPointsEquiv G (flagProjection G 1))
    rw [partialFlagMorphism_points G {i} (flagProjection G (g⁻¹ * h)),
      partialFlagMorphism_points G {i} (flagProjection G 1)]
    symm
    apply congrArg (partialFlagPointsEquiv G {i})
    apply (partialFlagProjection_eq G {i} 1 (g⁻¹ * h)).mpr
    simpa only [inv_one, one_mul] using hrel
  obtain ⟨y, hy⟩ := (simple_point_fibre G i
    (flagVarietyPointsEquiv G (flagProjection G (g⁻¹ * h)))).mpr hbase
  have hendpoint : reductivePointsMulEquiv G g •
      Variety.mapPoints (simpleInclusion G i) y =
        flagVarietyPointsEquiv G (flagProjection G h) := by
    rw [hy, flagVarietyAction_points G g, ← flagProjection_smul, mul_inv_cancel_left]
  exact ⟨g, y, ha, hendpoint.trans hb⟩

private theorem point_incidence (q : (incidenceVariety G i).points)
    (g : G.points) (y : (simpleFibre G i).points)
    (ha : flagVarietyPointsEquiv G (flagProjection G g) =
      Variety.mapPoints (incidenceFst G i) q)
    (hb : reductivePointsMulEquiv G g • Variety.mapPoints (simpleInclusion G i) y =
      Variety.mapPoints (incidenceSnd G i) q) :
    flagBundlePoint G (simpleFibre G i) g y ≫ simpleIncidenceMap G i = q.val := by
  apply pullback.hom_ext
  · calc
      _ = flagBundlePoint G (simpleFibre G i) g y ≫
          flagBundleProjection G (simpleFibre G i) := by
        simp only [Category.assoc, simpleIncidenceMap, pullback.lift_fst]
      _ = (flagVarietyPointsEquiv G (flagProjection G g)).val :=
        flagBundlePoint_projection G (simpleFibre G i) g y
      _ = (Variety.mapPoints (incidenceFst G i) q).val := congrArg Subtype.val ha
      _ = _ := rfl
  · calc
      _ = flagBundlePoint G (simpleFibre G i) g y ≫
          flagBundleMap G (simpleFibre G i) (simpleInclusion G i) := by
        simp only [Category.assoc, simpleIncidenceMap, pullback.lift_snd]
      _ = (reductivePointsMulEquiv G g • Variety.mapPoints (simpleInclusion G i) y).val :=
        flagBundlePoint_map G (simpleFibre G i) (simpleInclusion G i) g y
      _ = (Variety.mapPoints (incidenceSnd G i) q).val := congrArg Subtype.val hb
      _ = _ := rfl

private theorem simpleIncidenceMap_surjective : Surjective (simpleIncidenceMap G i) := by
  have : IsClosedImmersion (simpleIncidenceMap G i) := simpleIncidenceMap_isClosed G i
  apply Variety.surjective_of_dense_points (incidenceVariety G i) (incidenceVariety G i)
    (simpleIncidenceMap G i) (𝟙 (incidenceVariety G i).toOver)
  · change DenseRange (id : (incidenceVariety G i).scheme → (incidenceVariety G i).scheme)
    exact denseRange_id
  · intro q
    rw [Variety.mapPoints_id]
    obtain ⟨g, y, ha, hb⟩ := compatible_preimage G i q
    have hlift := point_incidence G i q g y ha hb
    refine ⟨flagBundlePoint G (simpleFibre G i) g y (IsLocalRing.closedPoint K), ?_⟩
    exact congrArg (fun f => f (IsLocalRing.closedPoint K)) hlift

/-- The simple associated flag bundle is the incidence of two flags with the same partial flag. -/
theorem simpleSchubert_incidence :
    ∃ e : flagBundleScheme G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) ≅
          pullback (partialFlagMorphism G {i}).left (partialFlagMorphism G {i}).left,
      (e.hom ≫ pullback.fst (partialFlagMorphism G {i}).left
          (partialFlagMorphism G {i}).left = flagBundleProjection G
            (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) ∧
      (e.hom ≫ pullback.snd (partialFlagMorphism G {i}).left
          (partialFlagMorphism G {i}).left = flagBundleMap G
            (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
            (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) := by
  have : IsClosedImmersion (simpleIncidenceMap G i) := simpleIncidenceMap_isClosed G i
  have : Surjective (simpleIncidenceMap G i) := simpleIncidenceMap_surjective G i
  have : IsReduced (incidenceVariety G i).scheme := (incidenceVariety G i).reduced
  have : IsIso (simpleIncidenceMap G i) :=
    isIso_of_isClosedImmersion_of_surjective (simpleIncidenceMap G i)
  refine ⟨asIso (simpleIncidenceMap G i), ?_, ?_⟩
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_snd _ _ _

end SchubertGeometry
