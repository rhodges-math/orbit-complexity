import OrbitComplexity.SchubertGeometry.BSDH.EndpointCharts

/-! # Regular lifts to intersections of flag charts -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace SchubertGeometry

/-- A regular group-valued map acts on the second factor of a product over the base. -/
def overlapTwist {S : Scheme.{u}} {H Z Y : Over S}
    [GrpObj H] [ModObj H Y] (b : Z ⟶ H) : Z ⊗ Y ≅ Z ⊗ Y where
  hom := lift (fst Z Y) ((fst Z Y ≫ b) • snd Z Y)
  inv := lift (fst Z Y) ((fst Z Y ≫ b)⁻¹ • snd Z Y)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [ModObj.comp_smul, GrpObj.comp_inv]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [ModObj.comp_smul]

private theorem overlapTwist_fst {S : Scheme.{u}} {H Z Y : Over S}
    [GrpObj H] [ModObj H Y] (b : Z ⟶ H) :
    (overlapTwist (Y := Y) b).hom ≫ fst Z Y = fst Z Y := by
  simp [overlapTwist]

private theorem overlapTwist_snd {S : Scheme.{u}} {H Z Y : Over S}
    [GrpObj H] [ModObj H Y] (b : Z ⟶ H) :
    (overlapTwist (Y := Y) b).hom ≫ snd Z Y = (fst Z Y ≫ b) • snd Z Y := by
  simp [overlapTwist]

private theorem overlapTwist_comp {S : Scheme.{u}} {H Z Y : Over S}
    [GrpObj H] [ModObj H Y] (b c : Z ⟶ H) :
    (overlapTwist (Y := Y) b).hom ≫ (overlapTwist (Y := Y) c).hom =
      (overlapTwist (Y := Y) (c * b)).hom := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [overlapTwist, ModObj.comp_smul, MonObj.comp_mul, mul_smul]

private theorem exists_flagOverlapLift {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (G : ReductiveGroups.ReductiveGroupData K) (g h : G.points)
    (Z : Over (Spec (.of K)))
    (a b : Z ⟶ (GroupActions.oppositeUnipotentVariety G).toOver)
    (hab : a.left ≫ flagSchemeChart G g = b.left ≫ flagSchemeChart G h) :
    ∃ x : Z ⟶ (flagOverlapVariety G g h).toOver,
      x ≫ flagOverlapInclusion G g h = a ∧ x ≫ flagOverlapCoordinate G g h = b := by
  let L := (flagGlueData G).vPullbackConeIsLimit g h
  let x : Z.left ⟶ (flagOverlapVariety G g h).scheme :=
    PullbackCone.IsLimit.lift L a.left b.left hab
  have hx : x ≫ (flagOverlapInclusion G g h).left = a.left :=
    PullbackCone.IsLimit.lift_fst L a.left b.left hab
  have hy' := PullbackCone.IsLimit.lift_snd L a.left b.left hab
  change x ≫ ((flagTransition G g h).left ≫
    (flagOverlapInclusion G h g).left) = b.left at hy'
  have hy : x ≫ (flagOverlapCoordinate G g h).left = b.left := by
    rw [← flagTransition_comp G g h]
    exact hy'
  have hw : (flagOverlapInclusion G g h).left ≫
      (GroupActions.oppositeUnipotentVariety G).toSpec =
        (flagOverlapVariety G g h).toSpec := (flagOverlapInclusion G g h).w
  have hspec : x ≫ (flagOverlapVariety G g h).toSpec = Z.hom := by
    rw [← hw, ← Category.assoc, hx]
    exact a.w
  refine ⟨Over.homMk x hspec, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact hx
  · apply Over.OverMorphism.ext
    exact hy

private theorem flagBundleOverlap_tensor {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (G : ReductiveGroups.ReductiveGroupData K)
    (Y : GroupActions.Variety K) [ModObj (GroupActions.borelVariety G).toOver Y.toOver]
    (g h : G.points) (Z : Over (Spec (.of K)))
    (x : Z ⟶ (flagOverlapVariety G g h).toOver) :
    (x ⊗ₘ 𝟙 Y.toOver) ≫ flagBundleTransition G Y g h ≫
        flagBundleInclusion G Y h g =
      (overlapTwist (Y := Y.toOver) (x ≫ flagOverlapBorel G g h)).hom ≫
        ((x ≫ flagOverlapCoordinate G g h) ⊗ₘ 𝟙 Y.toOver) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, flagBundleInclusion, tensorHom_fst]
    rw [← Category.assoc (flagBundleTransition G Y g h), flagBundleTransition_fst]
    simp only [Category.assoc, tensorHom_fst_assoc, overlapTwist, lift_fst_assoc]
    rw [flagTransition_comp]
  · simp only [Category.assoc, flagBundleInclusion, tensorHom_snd, Category.comp_id]
    rw [flagBundleTransition_snd]
    simp only [ModObj.comp_smul, tensorHom_fst_assoc, tensorHom_snd,
      Category.comp_id, overlapTwist_snd]

private theorem flagBundleOverlap_chart {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (G : ReductiveGroups.ReductiveGroupData K)
    (Y : GroupActions.Variety K) [ModObj (GroupActions.borelVariety G).toOver Y.toOver]
    (g h : G.points) (Z : Over (Spec (.of K)))
    (x : Z ⟶ (flagOverlapVariety G g h).toOver) :
    ((x ≫ flagOverlapInclusion G g h) ⊗ₘ 𝟙 Y.toOver).left ≫
        flagBundleChart G Y g =
      (overlapTwist (Y := Y.toOver) (x ≫ flagOverlapBorel G g h)).hom.left ≫
        ((x ≫ flagOverlapCoordinate G g h) ⊗ₘ 𝟙 Y.toOver).left ≫
          flagBundleChart G Y h := by
  have hglue := (flagBundleGlueData G Y).glue_condition g h
  change (flagBundleTransition G Y g h).left ≫
      (flagBundleInclusion G Y h g).left ≫ flagBundleChart G Y h =
    (flagBundleInclusion G Y g h).left ≫ flagBundleChart G Y g at hglue
  have he := congrArg (fun f ↦ f.left ≫ flagBundleChart G Y h)
    (flagBundleOverlap_tensor G Y g h Z x)
  have hincl : (x ⊗ₘ 𝟙 Y.toOver) ≫ flagBundleInclusion G Y g h =
      ((x ≫ flagOverlapInclusion G g h) ⊗ₘ 𝟙 Y.toOver) := by
    simp only [flagBundleInclusion, tensorHom_comp_tensorHom, Category.comp_id]
  rw [← hincl]
  change (x ⊗ₘ 𝟙 Y.toOver).left ≫ (flagBundleInclusion G Y g h).left ≫
    flagBundleChart G Y g = _
  rw [← hglue]
  simpa only [Over.comp_left, Category.assoc] using he

private theorem exists_bundleChart_overlap {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (G : ReductiveGroups.ReductiveGroupData K)
    (Y : GroupActions.Variety K) [ModObj (GroupActions.borelVariety G).toOver Y.toOver]
    (g h : G.points) (Z : Over (Spec (.of K)))
    (a b : Z ⟶ (GroupActions.oppositeUnipotentVariety G).toOver)
    (hab : a.left ≫ flagSchemeChart G g = b.left ≫ flagSchemeChart G h) :
    ∃ β : Z ⟶ (GroupActions.borelVariety G).toOver,
      a ≫ flagChartMap G g = (b ≫ flagChartMap G h) *
        (β ≫ GroupActions.borelInclusion G) ∧
      (a ⊗ₘ 𝟙 Y.toOver).left ≫ flagBundleChart G Y g =
        (overlapTwist (Y := Y.toOver) β).hom.left ≫
          (b ⊗ₘ 𝟙 Y.toOver).left ≫ flagBundleChart G Y h := by
  obtain ⟨x, hx, hy⟩ := exists_flagOverlapLift G g h Z a b hab
  refine ⟨x ≫ flagOverlapBorel G g h, ?_, ?_⟩
  · have hs := congrArg (fun f ↦ x ≫ f) (flagTorsor_section G g h)
    simpa only [MonObj.comp_mul, ← Category.assoc, hx, hy] using hs
  · simpa only [hx, hy] using flagBundleOverlap_chart G Y g h Z x

private theorem bsdh_append_hom_ext {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (G : ReductiveGroups.ReductiveGroupData K)
    (word : List G.rootBase.support) (i : G.rootBase.support)
    {Z : Scheme.{u}} (f g : Z ⟶ bsdhScheme G (word ++ [i]))
    (hfst : f ≫ bsdhAppendFst G word i = g ≫ bsdhAppendFst G word i)
    (hsnd : f ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      g ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)))) : f = g := by
  have : IsIso (bsdhAppendIso G word i).hom.left := inferInstance
  apply (cancel_mono (bsdhAppendIso G word i).hom.left).mp
  apply pullback.hom_ext
  · exact hfst
  · exact hsnd

/-- Regular flag lifts identify append charts through their Borel transition factor. -/
theorem bsdh_chart_transition {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (G : ReductiveGroups.ReductiveGroupData K)
    (word : List G.rootBase.support) (i : G.rootBase.support)
    (U V Z : Over (Spec (.of K)))
    (bU : U ⟶ Over.mk (bsdhToSpec G word))
    (bV : V ⟶ Over.mk (bsdhToSpec G word))
    (p : Z ⟶ U) (q : Z ⟶ V) (hpq : p ≫ bU = q ≫ bV)
    (g h : G.points)
    (aU : U ⟶ (GroupActions.oppositeUnipotentVariety G).toOver)
    (aV : V ⟶ (GroupActions.oppositeUnipotentVariety G).toOver)
    (hU : aU.left ≫ flagSchemeChart G g = bU.left ≫ bsdhMap G word)
    (hV : aV.left ≫ flagSchemeChart G h = bV.left ≫ bsdhMap G word)
    (cU : U ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (cV : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hfU : (fst U _).left ≫ bU.left = cU.left ≫ bsdhAppendFst G word i)
    (hfV : (fst V _).left ≫ bV.left = cV.left ≫ bsdhAppendFst G word i)
    (heU : cU.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (aU ⊗ₘ 𝟙 _).left ≫ flagBundleChart G _ g)
    (heV : cV.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (aV ⊗ₘ 𝟙 _).left ≫ flagBundleChart G _ h) :
    let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    ∃ β : Z ⟶ (GroupActions.borelVariety G).toOver,
      (p ≫ aU) ≫ flagChartMap G g = ((q ≫ aV) ≫ flagChartMap G h) *
        (β ≫ GroupActions.borelInclusion G) ∧
      (p ⊗ₘ 𝟙 Y.toOver) ≫ cU =
        (overlapTwist (Y := Y.toOver) β).hom ≫ (q ⊗ₘ 𝟙 Y.toOver) ≫ cV := by
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  have hab : (p ≫ aU).left ≫ flagSchemeChart G g =
      (q ≫ aV).left ≫ flagSchemeChart G h := by
    simp only [Over.comp_left, Category.assoc, hU, hV]
    exact congrArg (fun f ↦ f.left ≫ bsdhMap G word) hpq
  obtain ⟨β, hs, hβ⟩ := exists_bundleChart_overlap G Y g h Z (p ≫ aU) (q ≫ aV) hab
  refine ⟨β, hs, ?_⟩
  apply Over.OverMorphism.ext
  apply bsdh_append_hom_ext G word i
  · simp only [Over.comp_left, Category.assoc, ← hfU, ← hfV]
    have hbase : (p ⊗ₘ 𝟙 Y.toOver) ≫ fst U Y.toOver ≫ bU =
        (overlapTwist (Y := Y.toOver) β).hom ≫
          (q ⊗ₘ 𝟙 Y.toOver) ≫ fst V Y.toOver ≫ bV := by
      simpa only [Category.assoc, tensorHom_fst_assoc, overlapTwist, lift_fst_assoc] using
        congrArg (fun f ↦ fst Z Y.toOver ≫ f) hpq
    simpa only [Over.comp_left, Category.assoc] using congrArg Over.Hom.left hbase
  · simp only [Over.comp_left, Category.assoc, heU, heV]
    simpa only [← Category.assoc, ← Over.comp_left, tensorHom_comp_tensorHom,
      Category.comp_id] using hβ

end SchubertGeometry
