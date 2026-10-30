import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares
import OrbitComplexity.SchubertGeometry.Normality.SchubertImageStages
import OrbitComplexity.FrobeniusSplitting.Compatible.Pushforward
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Schubert image maps on the prescribed coefficient models

A reduced-word endpoint descends between the specified face and Schubert
models while retaining its triangle in the ambient flag model. The image
kernel comparison then persists on field fibres.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite FrobeniusSplitting
open ReductiveGroups

open private generic_endpoint_triangle from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.PointedIsoStages
open private scalarLeg_snd from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent
open private scalarLeg_fst from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelStageMaps
open private modelMap_base from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoDescent
open private modelComparison modelComparison_projection from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares

namespace SchubertGeometry

private theorem map_base_triangle {C : Type*} [Category C] {A B D E Z : C}
    (f : A ⟶ B) (q : B ⟶ D) (j : D ⟶ E) (a : D ⟶ Z) (b : E ⟶ Z)
    (hj : j ≫ b = a) : (f ≫ q ≫ j) ≫ b = (f ≫ q) ≫ a := by
  calc
    (f ≫ q ≫ j) ≫ b = f ≫ q ≫ (j ≫ b) := by simp only [Category.assoc]
    _ = f ≫ q ≫ a := congrArg (fun k => f ≫ q ≫ k) hj
    _ = (f ≫ q) ≫ a := (Category.assoc _ _ _).symm

private theorem comp_base_triangle {C : Type*} [Category C] {A B D Z : C}
    (q : A ⟶ B) (i : B ⟶ D) (a : B ⟶ Z) (b : D ⟶ Z)
    (hi : i ≫ b = a) : (q ≫ i) ≫ b = q ≫ a :=
  (Category.assoc _ _ _).trans (congrArg (fun k => q ≫ k) hi)

private theorem postcompose_agreement {C : Type*} [Category C] {A B D Z : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (j : D ⟶ Z)
    (hg : f ≫ g = h) : f ≫ (g ≫ j) = h ≫ j :=
  (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ j) hg)

private theorem transport_map_triangle {C : Type*} [Category C]
    {A B A' B' Z : C} (f : A ⟶ B) (f' : A' ⟶ B') (u : A' ⟶ A) (v : B' ⟶ B)
    (qA : A ⟶ Z) (qB : B ⟶ Z) (qA' : A' ⟶ Z) (qB' : B' ⟶ Z)
    (hf : f' ≫ v = u ≫ f) (hA : u ≫ qA = qA') (hB : v ≫ qB = qB')
    (h : u ≫ f ≫ qB = u ≫ qA) : f' ≫ qB' = qA' := by
  calc
    f' ≫ qB' = f' ≫ (v ≫ qB) := congrArg (fun k => f' ≫ k) hB.symm
    _ = (f' ≫ v) ≫ qB := (Category.assoc _ _ _).symm
    _ = (u ≫ f) ≫ qB := congrArg (fun k => k ≫ qB) hf
    _ = u ≫ qA := (Category.assoc _ _ _).trans h
    _ = qA' := hA

/-- A morphism between the extensions of prescribed models descends above
any coefficient stage, retaining both its generic comparison and its triangle
in the specified ambient model. -/
theorem exists_model_morphism_commuting {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG)
    (C D F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [LocallyOfFinitePresentation D.hom] [LocallyOfFiniteType F.hom]
    (i : C ⟶ F) (j : D ⟶ F)
    (g : genericScalarModel S C.hom ⟶ genericScalarModel S D.hom)
    (hg : g.left ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) D.hom ≫ j.left =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) C.hom ≫ i.left)
    (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t)
      (gt : stageScalarModel S C.hom t ⟶ stageScalarModel S D.hom t),
      gt.left ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          D.hom ≫ j.left =
        pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          C.hom ≫ i.left ∧
      (modelScalarCone S C.hom).π.app (op t) ≫ gt.left =
        g.left ≫ (modelScalarCone S D.hom).π.app (op t) := by
  obtain ⟨r, gr, hgr⟩ := exists_model_morphism S hS C.hom D.hom g
  obtain ⟨s, hrs, hstart⟩ := exists_ge_ge r start
  let gs := extendModelMorphism S C.hom D.hom hrs gr
  have hgs := extendModelMorphism_baseChange S C.hom D.hom hrs gr g hgr
  let qC := pullback.snd
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion s.property.2).toRingHom)) C.hom
  let qD := pullback.snd
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion s.property.2).toRingHom)) D.hom
  have hbaseLeft : (gs.left ≫ qD ≫ j.left) ≫ F.hom =
      (modelScalarBase S C.hom).app (op s) := by
    have hbase : (gs.left ≫ qD) ≫ D.hom =
        (modelScalarBase S C.hom).app (op s) := modelMap_base S C.hom D.hom s gs
    exact (map_base_triangle gs.left qD j.left D.hom F.hom j.w).trans hbase
  have hbaseRight : (qC ≫ i.left) ≫ F.hom =
      (modelScalarBase S C.hom).app (op s) := by
    have hbase : qC ≫ C.hom = (modelScalarBase S C.hom).app (op s) := rfl
    exact (comp_base_triangle qC i.left C.hom F.hom i.w).trans hbase
  let πC : (genericScalarModel S C.hom).left ⟶ (stageScalarModel S C.hom s).left :=
    (modelScalarCone S C.hom).π.app (op s)
  let πD : (genericScalarModel S D.hom).left ⟶ (stageScalarModel S D.hom s).left :=
    (modelScalarCone S D.hom).π.app (op s)
  let rC : (genericScalarModel S C.hom).left ⟶ C.left :=
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) C.hom
  let rD : (genericScalarModel S D.hom).left ⟶ D.left :=
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) D.hom
  have hgs' : πC ≫ gs.left = g.left ≫ πD := hgs
  have hprojectionC : πC ≫ qC = rC := scalarLeg_snd S C.hom s
  have hprojectionD : πD ≫ qD = rD := scalarLeg_snd S D.hom s
  have hg' : g.left ≫ rD ≫ j.left = rC ≫ i.left := hg
  have hgeneric₀ : πC ≫ gs.left ≫ qD ≫ j.left = πC ≫ qC ≫ i.left :=
    generic_endpoint_triangle πC πD g.left gs.left qC qD rC rD i.left j.left
      hgs' hprojectionC hprojectionD hg'
  have hgeneric : (modelScalarCone S C.hom).π.app (op s) ≫
      (gs.left ≫ qD ≫ j.left) =
      (modelScalarCone S C.hom).π.app (op s) ≫ (qC ≫ i.left) :=
    hgeneric₀
  obtain ⟨t, hst, htriangle⟩ := exists_scalar_equality S hS C.hom F.hom s
    (gs.left ≫ qD ≫ j.left) (qC ≫ i.left) hbaseLeft hbaseRight hgeneric
  let gt := extendModelMorphism S C.hom D.hom hst gs
  have hqC : stageScalarTransition S C.hom hst ≫ qC = pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) C.hom :=
    stageScalarTransition_snd S C.hom hst
  have hqD : stageScalarTransition S D.hom hst ≫ qD = pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) D.hom :=
    stageScalarTransition_snd S D.hom hst
  refine ⟨t, hstart.trans hst, gt, ?_, ?_⟩
  · exact transport_map_triangle gs.left gt.left
      (stageScalarTransition S C.hom hst) (stageScalarTransition S D.hom hst)
      (qC ≫ i.left) (qD ≫ j.left) _ _
      (extendModelMorphism_transition S C.hom D.hom hst gs)
      (postcompose_agreement _ qC _ i.left hqC)
      (postcompose_agreement _ qD _ j.left hqD) htriangle
  · exact extendModelMorphism_baseChange S C.hom D.hom hst gs g hgs

private def transportOverMap {B : Scheme.{u}} {X Y X' Y' : Over B}
    (α : X ≅ X') (β : Y ≅ Y') (f : X ⟶ Y) : X' ⟶ Y' :=
  α.inv ≫ f ≫ β.hom

private theorem transportOverMap_triangle {B : Scheme.{u}}
    {X Y X' Y' : Over B} (α : X ≅ X') (β : Y ≅ Y') (f : X ⟶ Y)
    {A D Z : Scheme.{u}} (qX : X.left ⟶ A) (qY : Y.left ⟶ D)
    (qX' : X'.left ⟶ A) (qY' : Y'.left ⟶ D) (a : A ⟶ Z) (b : D ⟶ Z)
    (hα : α.hom.left ≫ qX' = qX) (hβ : β.hom.left ≫ qY' = qY)
    (hf : f.left ≫ qY ≫ b = qX ≫ a) :
    (transportOverMap α β f).left ≫ qY' ≫ b = qX' ≫ a := by
  change (α.inv.left ≫ f.left ≫ β.hom.left) ≫ qY' ≫ b = _
  have hβb : β.hom.left ≫ qY' ≫ b = qY ≫ b :=
    postcompose_agreement β.hom.left qY' qY b hβ
  calc
    (α.inv.left ≫ f.left ≫ β.hom.left) ≫ qY' ≫ b =
        α.inv.left ≫ f.left ≫ (β.hom.left ≫ qY' ≫ b) := by simp only [Category.assoc]
    _ = α.inv.left ≫ f.left ≫ qY ≫ b :=
      congrArg (fun k => α.inv.left ≫ f.left ≫ k) hβb
    _ = α.inv.left ≫ qX ≫ a := by rw [hf]
    _ = α.inv.left ≫ (α.hom.left ≫ qX') ≫ a := by rw [hα]
    _ = qX' ≫ a := by
      have hcancel : α.inv.left ≫ α.hom.left = 𝟙 X'.left :=
        congrArg (fun k => k.left) α.inv_hom_id
      calc
        α.inv.left ≫ (α.hom.left ≫ qX') ≫ a =
            (α.inv.left ≫ α.hom.left) ≫ (qX' ≫ a) := by simp only [Category.assoc]
        _ = qX' ≫ a := by rw [hcancel, Category.id_comp]

private theorem transportOverMap_comparison {B : Scheme.{u}}
    {X Y X' Y' : Over B} (α : X ≅ X') (β : Y ≅ Y') (f : X ⟶ Y)
    {A D : Scheme.{u}} (a : X'.left ⟶ A) (b : Y'.left ⟶ D) (e : A ⟶ D)
    (he : a ≫ e = (transportOverMap α β f).left ≫ b) :
    (α.hom.left ≫ a) ≫ e = f.left ≫ (β.hom.left ≫ b) := by
  rw [Category.assoc, he]
  change α.hom.left ≫ ((α.inv.left ≫ f.left ≫ β.hom.left) ≫ b) = _
  simp only [Category.assoc]
  rw [← Category.assoc α.hom.left α.inv.left]
  have hcancel : α.hom.left ≫ α.inv.left = 𝟙 X.left :=
    congrArg (fun k => k.left) α.hom_inv_id
  rw [hcancel, Category.id_comp]

private theorem over_source_cartesian {B T Y : Scheme.{u}} {U V : Over T}
    (e : U ≅ V) (q : V.left ⟶ Y) (a : Y ⟶ B) (κ : T ⟶ B)
    (hp : IsPullback q V.hom a κ) : IsPullback (e.hom.left ≫ q) U.hom a κ := by
  have he : IsPullback e.hom.left U.hom V.hom (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact e.hom.w⟩
  simpa only [Category.id_comp] using he.paste_horiz hp

private theorem genericStage_cartesian {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (M : Over (Spec (.of S))) (t : CoefficientStage S) :
    IsPullback ((modelScalarCone S M.hom).π.app (op t))
      (genericScalarModel S M.hom).hom (stageScalarModel S M.hom t).hom
      (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) := by
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let κt := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap t.val K))
  have hρ : ρ ≫ κt = κ := by rw [← Spec.map_comp]; rfl
  have hprojection : (modelScalarCone S M.hom).π.app (op t) ≫ pullback.snd κt M.hom =
      pullback.snd κ M.hom := scalarLeg_snd S M.hom t
  have hbase : (modelScalarCone S M.hom).π.app (op t) ≫
      (stageScalarModel S M.hom t).hom = (genericScalarModel S M.hom).hom ≫ ρ :=
    scalarLeg_fst S M.hom t
  have houter : IsPullback
      ((modelScalarCone S M.hom).π.app (op t) ≫ pullback.snd κt M.hom)
      (genericScalarModel S M.hom).hom M.hom (ρ ≫ κt) := by
    rw [hprojection, hρ]
    exact (IsPullback.of_hasPullback κ M.hom).flip
  exact houter.of_right hbase
    (IsPullback.of_hasPullback κt M.hom).flip

/-- The reduced-word Schubert endpoint descends between the prescribed face
and Schubert models, keeping its triangle in the original ambient flag model. -/
theorem exists_word_image_morphism_stage {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (v : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced v)
    (S : Subalgebra ℤ K) (hS : S.FG) (C D F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [LocallyOfFinitePresentation D.hom] [LocallyOfFiniteType F.hom]
    (i : C ⟶ F) (j : D ⟶ F)
    (qC : (bsdhVariety G v).toOver.left ⟶ C.left)
    (qD : (schubertVariety G (simpleWeylWord G.rootBase v)).toOver.left ⟶ D.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hC : IsPullback qC (bsdhVariety G v).toOver.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD
      (schubertVariety G (simpleWeylWord G.rootBase v)).toOver.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hi : bsdhMap G v ≫ qF = qC ≫ i.left)
    (hj : (schubertInclusion G (simpleWeylWord G.rootBase v)).left ≫ qF = qD ≫ j.left)
    (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t)
      (e : stageScalarModel S C.hom t ⟶ stageScalarModel S D.hom t),
      e.left ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          D.hom ≫ j.left =
        pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          C.hom ≫ i.left ∧
      ∃ (qCt : (bsdhVariety G v).toOver.left ⟶ (stageScalarModel S C.hom t).left)
        (qDt : (schubertVariety G (simpleWeylWord G.rootBase v)).toOver.left ⟶
          (stageScalarModel S D.hom t).left),
        IsPullback qCt (bsdhVariety G v).toOver.hom (stageScalarModel S C.hom t).hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
        IsPullback qDt (schubertVariety G (simpleWeylWord G.rootBase v)).toOver.hom
          (stageScalarModel S D.hom t).hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
        qCt ≫ e.left = (bsdhSchubertMap G v hred).left ≫ qDt := by
  let α : (bsdhVariety G v).toOver ≅ genericScalarModel S C.hom :=
    modelComparison _ C qC hC
  let β : (schubertVariety G (simpleWeylWord G.rootBase v)).toOver ≅
      genericScalarModel S D.hom := modelComparison _ D qD hD
  have hendpoint : (bsdhSchubertMap G v hred).left ≫ qD ≫ j.left = qC ≫ i.left := by
    calc
      (bsdhSchubertMap G v hred).left ≫ qD ≫ j.left =
          (bsdhSchubertMap G v hred).left ≫
            (schubertInclusion G (simpleWeylWord G.rootBase v)).left ≫ qF := by rw [hj]
      _ = bsdhMap G v ≫ qF := by rw [← Category.assoc, bsdhSchubertMap_comp]
      _ = qC ≫ i.left := hi
  let g := transportOverMap α β (bsdhSchubertMap G v hred)
  have hg := transportOverMap_triangle α β (bsdhSchubertMap G v hred) qC qD
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) C.hom)
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) D.hom)
    i.left j.left (modelComparison_projection _ C qC hC)
    (modelComparison_projection _ D qD hD) hendpoint
  obtain ⟨t, hstart, e, he, heK⟩ := exists_model_morphism_commuting S hS C D F i j g hg start
  refine ⟨t, hstart, e, he, α.hom.left ≫ (modelScalarCone S C.hom).π.app (op t),
    β.hom.left ≫ (modelScalarCone S D.hom).π.app (op t), ?_, ?_, ?_⟩
  · exact over_source_cartesian α _ _ _ (genericStage_cartesian S C t)
  · exact over_source_cartesian β _ _ _ (genericStage_cartesian S D t)
  · exact transportOverMap_comparison α β (bsdhSchubertMap G v hred) _ _ e.left heK

/-- The prescribed reduced-word face has the original Schubert image ideal
on all field fibres above one coefficient stage. Compatibility of that face
therefore gives compatibility of the Schubert ideal for the same splitting
pushed forward to the ambient scheme. -/
theorem exists_word_image_kernel_stage {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (v : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced v)
    (S : Subalgebra ℤ K) (hS : S.FG) (C D F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [CompactSpace D.left] [QuasiSeparatedSpace D.left]
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation D.hom]
    [LocallyOfFiniteType F.hom] (i : C ⟶ F) (j : D ⟶ F)
    (qC : (bsdhVariety G v).toOver.left ⟶ C.left)
    (qD : (schubertVariety G (simpleWeylWord G.rootBase v)).toOver.left ⟶ D.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hC : IsPullback qC (bsdhVariety G v).toOver.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD
      (schubertVariety G (simpleWeylWord G.rootBase v)).toOver.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hi : bsdhMap G v ≫ qF = qC ≫ i.left)
    (hj : (schubertInclusion G (simpleWeylWord G.rootBase v)).left ≫ qF = qD ≫ j.left)
    (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t)
      (e : stageScalarModel S C.hom t ⟶ stageScalarModel S D.hom t),
      e.left ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          D.hom ≫ j.left =
        pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          C.hom ≫ i.left ∧
      ∃ R : Subalgebra ℤ K, R.FG ∧ t.val ≤ R ∧ ∃ hTR : t.val ≤ R,
        ∀ (L : Type u) [Field L] [Algebra R L]
          (XL YL : Over (Spec (.of L))) (fL : XL ⟶ YL) [QuasiCompact fL.left]
          (qXL : XL.left ⟶ (stageScalarModel S C.hom t).left)
          (qYL : YL.left ⟶ (stageScalarModel S D.hom t).left)
          (_hXL : IsPullback qXL XL.hom (stageScalarModel S C.hom t).hom
            (Spec.map (CommRingCat.ofHom
              ((algebraMap R L).comp (Subalgebra.inclusion hTR).toRingHom))))
          (_hYL : IsPullback qYL YL.hom (stageScalarModel S D.hom t).hom
            (Spec.map (CommRingCat.ofHom
              ((algebraMap R L).comp (Subalgebra.inclusion hTR).toRingHom))))
          (_hfL : fL.left ≫ qYL = qXL ≫ e.left),
          IsSchemeTheoreticallyDominant fL.left ∧
          ∀ (Z : Scheme.{u}) (jL : YL.left ⟶ Z),
            (fL.left ≫ jL).ker = jL.ker ∧
            ∀ (W : Scheme.{u}) (p : ℕ) (splitting : SchemeSplitting W p)
              (a : XL.left ⟶ W) [QuasiCompact a]
              (endpoint : W ⟶ Z) [QuasiCompact endpoint] [IsIso endpoint.c]
              (_hendpoint : a ≫ endpoint = fL.left ≫ jL)
              (_hcompatible : splitting.IsCompatible a.ker),
              (splitting.pushforward endpoint).IsCompatible jL.ker := by
  obtain ⟨t, hstart, e, he, qCt, qDt, hCt, hDt, heK⟩ :=
    exists_word_image_morphism_stage G v hred S hS C D F i j qC qD qF hC hD hi hj start
  let Ct := stageScalarModel S C.hom t
  let Dt := stageScalarModel S D.hom t
  let : CompactSpace Ct.left := by
    change CompactSpace ↥(pullback
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) C.hom : Scheme)
    infer_instance
  let : CompactSpace Dt.left := by
    change CompactSpace ↥(pullback
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) D.hom : Scheme)
    infer_instance
  let : QuasiSeparatedSpace Dt.left := by
    change QuasiSeparatedSpace ↥(pullback
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) D.hom : Scheme)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) D.hom)
  let : LocallyOfFinitePresentation Ct.hom := by
    change LocallyOfFinitePresentation (pullback.fst _ C.hom)
    infer_instance
  let : LocallyOfFinitePresentation Dt.hom := by
    change LocallyOfFinitePresentation (pullback.fst _ D.hom)
    infer_instance
  let : QuasiCompact e.left := inferInstance
  obtain ⟨R, hR, hTR, hTR', hkernel⟩ := exists_schubert_kernel_stage G v hred
    t.val t.property.1 Ct Dt e qCt qDt hCt hDt heK t.val t.property.1
  refine ⟨t, hstart, e, he, R, hR, hTR, hTR', ?_⟩
  intro L _ _ XL YL fL _ qXL qYL hXL hYL hfL
  obtain ⟨hdominant, hker⟩ := hkernel L XL YL fL qXL qYL hXL hYL hfL
  refine ⟨hdominant, ?_⟩
  intro Z jL
  refine ⟨hker Z jL, ?_⟩
  intro W p splitting a _ endpoint _ _ hendpoint hcompatible
  have hcomp := SchemeSplitting.IsCompatible.pushforward_ker splitting a endpoint hcompatible
  rw [hendpoint, hker Z jL] at hcomp
  exact hcomp

end SchubertGeometry
