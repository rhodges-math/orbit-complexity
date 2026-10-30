import OrbitComplexity.FrobeniusSplitting.Normality.Limits.AffineOpenStages
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ScalarOpenIso
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionChartModels
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian

/-! # Opposition chart maps at coefficient stages

Comparing a fixed chart model with an open subscheme identifies its original
map to the ambient model with the open inclusion after coefficient extension.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting GroupActions ReductiveGroups
open scoped TensorProduct

namespace SchubertGeometry.DeterminantSection

open private modelComparison modelComparison_projection conjugate_triangle underlyingIso from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares
open private scalarLeg_fst scalarLeg_snd from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent
open private FrobeniusSplitting.RetainedCharacter.scalarMap from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
open private FrobeniusSplitting.scalar_polynomial_factor from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarPolynomialSquare
open private composite_projection from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionChartModels
open private chartAlgebra from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial

private def scalarMorphism {B T : Scheme.{u}} (β : T ⟶ B)
    {C F : Over B} (i : C ⟶ F) :
    Over.mk (pullback.fst β C.hom) ⟶ Over.mk (pullback.fst β F.hom) :=
  Over.homMk (pullback.lift (pullback.fst β C.hom)
    (pullback.snd β C.hom ≫ i.left) (by
      rw [Category.assoc, i.w]
      exact pullback.condition)) (pullback.lift_fst _ _ _)

private theorem scalarMorphism_projection {B T : Scheme.{u}} (β : T ⟶ B)
    {C F : Over B} (i : C ⟶ F) :
    (scalarMorphism β i).left ≫ pullback.snd β F.hom =
      pullback.snd β C.hom ≫ i.left :=
  pullback.lift_snd _ _ _

private theorem cartesian_map {B T : Scheme.{u}} (β : T ⟶ B)
    (C F : Over B) (CT FT : Over T) (i : C ⟶ F)
    (qC : CT.left ⟶ C.left) (qF : FT.left ⟶ F.left)
    (hC : IsPullback qC CT.hom C.hom β) (hF : IsPullback qF FT.hom F.hom β)
    (f : CT ⟶ FT) (hf : f.left ≫ qF = qC ≫ i.left) :
    IsPullback f.left qC qF i.left := by
  have houter : IsPullback (f.left ≫ FT.hom) qC β (i.left ≫ F.hom) := by
    rw [f.w, i.w]
    exact hC.flip
  exact houter.of_right hf hF.flip

private theorem intermediate_square {B T K : Scheme.{u}}
    (β : T ⟶ B) (κ : K ⟶ T) (γ : K ⟶ B) (hγ : κ ≫ β = γ)
    (C : Over B) (CT : Over T) (CK : Over K)
    (qT : CT.left ⟶ C.left) (qK : CK.left ⟶ C.left) (q : CK.left ⟶ CT.left)
    (hT : IsPullback qT CT.hom C.hom β) (hK : IsPullback qK CK.hom C.hom γ)
    (hq : q ≫ qT = qK) (hbase : q ≫ CT.hom = CK.hom ≫ κ) :
    IsPullback q CK.hom CT.hom κ := by
  have houter : IsPullback CK.hom (q ≫ qT) (κ ≫ β) C.hom := by
    rw [hq, hγ]
    exact hK.flip
  exact (houter.of_bot hbase.symm hT.flip).flip

private theorem naturality_square {B T K : Scheme.{u}} (β : T ⟶ B) (κ : K ⟶ T)
    (C F : Over B) (CT FT : Over T) (CK FK : Over K) (i : C ⟶ F)
    (iT : CT ⟶ FT) (iK : CK ⟶ FK)
    (qCT : CT.left ⟶ C.left) (qFT : FT.left ⟶ F.left)
    (qCK : CK.left ⟶ C.left) (qFK : FK.left ⟶ F.left)
    (pC : CK.left ⟶ CT.left) (pF : FK.left ⟶ FT.left)
    (hFT : IsPullback qFT FT.hom F.hom β)
    (hiT : iT.left ≫ qFT = qCT ≫ i.left)
    (hiK : iK.left ≫ qFK = qCK ≫ i.left)
    (hpC : pC ≫ qCT = qCK) (hpF : pF ≫ qFT = qFK)
    (hbC : pC ≫ CT.hom = CK.hom ≫ κ)
    (hbF : pF ≫ FT.hom = FK.hom ≫ κ) :
    pC ≫ iT.left = iK.left ≫ pF := by
  apply hFT.hom_ext
  · calc
      (pC ≫ iT.left) ≫ qFT = pC ≫ (qCT ≫ i.left) := by
        rw [Category.assoc, hiT]
      _ = qCK ≫ i.left := by rw [← Category.assoc, hpC]
      _ = iK.left ≫ qFK := hiK.symm
      _ = (iK.left ≫ pF) ≫ qFT := by rw [Category.assoc, hpF]
  · calc
      (pC ≫ iT.left) ≫ FT.hom = CK.hom ≫ κ := by
        rw [Category.assoc, iT.w, hbC]
      _ = iK.left ≫ (FK.hom ≫ κ) := by rw [← Category.assoc, iK.w]
      _ = (iK.left ≫ pF) ≫ FT.hom := by rw [Category.assoc, hbF]

private def cartesianLift {B T : Scheme.{u}} (β : T ⟶ B)
    (D F : Over B) (FT : Over T) (qF : FT.left ⟶ F.left)
    (hF : IsPullback qF FT.hom F.hom β) (j : D ⟶ F) :
    Over.mk (pullback.fst β D.hom) ⟶ FT :=
  Over.homMk (hF.lift (pullback.snd β D.hom ≫ j.left) (pullback.fst β D.hom) (by
    rw [Category.assoc, j.w]
    exact pullback.condition.symm)) (hF.lift_snd _ _ _)

private theorem cartesianLift_projection {B T : Scheme.{u}} (β : T ⟶ B)
    (D F : Over B) (FT : Over T) (qF : FT.left ⟶ F.left)
    (hF : IsPullback qF FT.hom F.hom β) (j : D ⟶ F) :
    (cartesianLift β D F FT qF hF j).left ≫ qF = pullback.snd β D.hom ≫ j.left :=
  hF.lift_fst _ _ _

private theorem iso_prefix_triangle {B : Scheme.{u}} {X Y Z : Over B}
    (α : X ≅ Y) (E : Y ≅ Z) {A D F : Scheme.{u}}
    (qX : X.left ⟶ A) (qY : Y.left ⟶ A) (qZ : Z.left ⟶ D)
    (i : A ⟶ F) (j : D ⟶ F) (hα : α.hom.left ≫ qY = qX)
    (hE : E.hom.left ≫ qZ ≫ j = qY ≫ i) :
    (α ≪≫ E).hom.left ≫ qZ ≫ j = qX ≫ i := by
  change (α.hom.left ≫ E.hom.left) ≫ qZ ≫ j = qX ≫ i
  rw [Category.assoc, hE, ← Category.assoc, hα]

private theorem generic_stage_cartesian {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (C : Over (Spec (.of S))) (t : CoefficientStage S) :
    IsPullback ((modelScalarCone S C.hom).π.app (op t))
      (genericScalarModel S C.hom).hom (stageScalarModel S C.hom t).hom
      (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) := by
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap t.val K)) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom) =
        Spec.map (CommRingCat.ofHom (algebraMap S K)) := by
    rw [← Spec.map_comp]
    rfl
  exact intermediate_square _ _ _ hbase C (stageScalarModel S C.hom t)
    (genericScalarModel S C.hom) _ _ ((modelScalarCone S C.hom).π.app (op t))
    (IsPullback.of_hasPullback _ _).flip (IsPullback.of_hasPullback _ _).flip
    (scalarLeg_snd S C.hom t) (scalarLeg_fst S C.hom t)

private theorem generic_naturality {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (C F : Over (Spec (.of S))) (i : C ⟶ F)
    (t : CoefficientStage S) :
    (modelScalarCone S C.hom).π.app (op t) ≫
        (scalarMorphism (Spec.map (CommRingCat.ofHom
          (Subalgebra.inclusion t.property.2).toRingHom)) i).left =
      (scalarMorphism (Spec.map (CommRingCat.ofHom (algebraMap S K))) i).left ≫
        (modelScalarCone S F.hom).π.app (op t) := by
  exact naturality_square _ _ C F (stageScalarModel S C.hom t)
    (stageScalarModel S F.hom t) (genericScalarModel S C.hom)
    (genericScalarModel S F.hom) i _ _ _ _ _ _ _ _
    (IsPullback.of_hasPullback _ _).flip
    (scalarMorphism_projection _ i) (scalarMorphism_projection _ i)
    (scalarLeg_snd S C.hom t) (scalarLeg_snd S F.hom t)
    (scalarLeg_fst S C.hom t) (scalarLeg_fst S F.hom t)

private theorem stage_naturality {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (C F : Over (Spec (.of S))) (i : C ⟶ F)
    {t r : CoefficientStage S} (htr : t ≤ r) :
    stageScalarTransition S C.hom htr ≫
        (scalarMorphism (Spec.map (CommRingCat.ofHom
          (Subalgebra.inclusion t.property.2).toRingHom)) i).left =
      (scalarMorphism (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion r.property.2).toRingHom)) i).left ≫
          stageScalarTransition S F.hom htr := by
  exact naturality_square _ _ C F (stageScalarModel S C.hom t)
    (stageScalarModel S F.hom t) (stageScalarModel S C.hom r)
    (stageScalarModel S F.hom r) i _ _ _ _ _ _ _ _
    (IsPullback.of_hasPullback _ _).flip
    (scalarMorphism_projection _ i) (scalarMorphism_projection _ i)
    (stageScalarTransition_snd S C.hom htr) (stageScalarTransition_snd S F.hom htr)
    (stageScalarTransition_fst S C.hom htr) (stageScalarTransition_fst S F.hom htr)

private theorem open_of_comparison {B T : Scheme.{u}} (β : T ⟶ B)
    (C D F : Over B) (CT DT FT : Over T) (i : C ⟶ F) (j : D ⟶ F)
    [IsOpenImmersion j.left]
    (qC : CT.left ⟶ C.left) (qD : DT.left ⟶ D.left) (qF : FT.left ⟶ F.left)
    (hD : IsPullback qD DT.hom D.hom β) (hF : IsPullback qF FT.hom F.hom β)
    (fC : CT ⟶ FT) (fD : DT ⟶ FT)
    (hCmap : fC.left ≫ qF = qC ≫ i.left)
    (hDmap : fD.left ≫ qF = qD ≫ j.left)
    (E : CT ≅ DT)
    (hE : E.hom.left ≫ qD ≫ j.left = qC ≫ i.left) :
    IsOpenImmersion fC.left := by
  have houter : IsPullback (fD.left ≫ FT.hom) qD β (j.left ≫ F.hom) := by
    rw [fD.w, j.w]
    exact hD.flip
  have hcart : IsPullback fD.left qD qF j.left :=
    houter.of_right hDmap hF.flip
  let : IsOpenImmersion fD.left := MorphismProperty.of_isPullback hcart.flip inferInstance
  have he : E.hom.left ≫ fD.left = fC.left := by
    apply hF.hom_ext
    · calc
        (E.hom.left ≫ fD.left) ≫ qF = E.hom.left ≫ (fD.left ≫ qF) :=
          Category.assoc _ _ _
        _ = E.hom.left ≫ (qD ≫ j.left) := congrArg (fun a => E.hom.left ≫ a) hDmap
        _ = qC ≫ i.left := hE
        _ = fC.left ≫ qF := hCmap.symm
    · calc
        (E.hom.left ≫ fD.left) ≫ FT.hom = E.hom.left ≫ DT.hom := by
          rw [Category.assoc, fD.w]
        _ = CT.hom := E.hom.w
        _ = fC.left ≫ FT.hom := fC.w.symm
  rw [← he]
  infer_instance

private theorem open_conjugate {X Y A B : Scheme.{u}}
    (α : X ≅ A) (β : Y ≅ B) (f : X ⟶ Y) (g : A ⟶ B)
    [IsOpenImmersion f] (h : α.hom ≫ g = f ≫ β.hom) :
    IsOpenImmersion g := by
  have heq : g = α.inv ≫ f ≫ β.hom := by
    calc
      g = α.inv ≫ (α.hom ≫ g) := by simp only [← Category.assoc, Iso.inv_hom_id,
        Category.id_comp]
      _ = α.inv ≫ (f ≫ β.hom) := congrArg (fun q => α.inv ≫ q) h
      _ = _ := (Category.assoc _ _ _).symm
  rw [heq]
  infer_instance

private theorem scalar_open_of_chart {B T : Scheme.{u}} (κ : T ⟶ B)
    (C F : Over B) (X Y : Over T) [IsAffine X.left]
    (i : C ⟶ F) (f : X ⟶ Y) [IsOpenImmersion f.left]
    (qC : X.left ⟶ C.left) (qF : Y.left ⟶ F.left)
    (hC : IsPullback qC X.hom C.hom κ) (hF : IsPullback qF Y.hom F.hom κ)
    (hf : f.left ≫ qF = qC ≫ i.left) :
    IsAffine (pullback κ C.hom) ∧ IsOpenImmersion (scalarMorphism κ i).left := by
  let α := modelComparison κ C qC hC
  let β := modelComparison κ F qF hF
  have hα : α.hom.left ≫ pullback.snd κ C.hom = qC :=
    modelComparison_projection κ C qC hC
  have hβ : β.hom.left ≫ pullback.snd κ F.hom = qF :=
    modelComparison_projection κ F qF hF
  have hmap : α.hom.left ≫ (scalarMorphism κ i).left = f.left ≫ β.hom.left :=
    naturality_square κ (𝟙 T) C F (Over.mk (pullback.fst κ C.hom))
      (Over.mk (pullback.fst κ F.hom)) X Y i (scalarMorphism κ i) f _ _ qC qF
      α.hom.left β.hom.left (IsPullback.of_hasPullback _ _).flip
      (scalarMorphism_projection κ i) hf hα hβ
      (by simpa only [Category.comp_id] using α.hom.w)
      (by simpa only [Category.comp_id] using β.hom.w)
  exact ⟨IsAffine.of_isIso (underlyingIso α).inv,
    open_conjugate (underlyingIso α) (underlyingIso β) f.left _ hmap⟩

private def openRangeIso {B : Scheme.{u}} (X Y : Over B) (f : X ⟶ Y)
    [IsOpenImmersion f.left] : X ≅ Over.mk (f.left.opensRange.ι ≫ Y.hom) :=
  Over.isoMk f.left.isoOpensRange (by
    change f.left.isoOpensRange.hom ≫ (f.left.opensRange.ι ≫ Y.hom) = X.hom
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    exact f.w)

private theorem compactBaseChange {B T X : Scheme.{u}} (β : T ⟶ B) (a : X ⟶ B)
    [QuasiCompact β] [CompactSpace X] : CompactSpace (pullback β a : Scheme.{u}) := by
  let : QuasiCompact (pullback.snd β a) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback β a) inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd β a)

private theorem exists_open_stage {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) (C F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left] [QuasiSeparatedSpace F.left]
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation F.hom]
    (i : C ⟶ F) [IsAffine (genericScalarModel S C.hom).left]
    [IsOpenImmersion (scalarMorphism
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) i).left]
    (start : CoefficientStage S) :
    ∃ (r : CoefficientStage S) (_ : start ≤ r), IsOpenImmersion
      (scalarMorphism (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion r.property.2).toRingHom)) i).left := by
  let iK : genericScalarModel S C.hom ⟶ genericScalarModel S F.hom :=
    scalarMorphism (Spec.map (CommRingCat.ofHom (algebraMap S K))) i
  let : IsOpenImmersion iK.left := by
    change IsOpenImmersion (scalarMorphism
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) i).left
    infer_instance
  let U := iK.left.opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange iK.left
  obtain ⟨t, hstartt, V, hV, hpreimage⟩ := exists_affine_opens_stage S hS
    (fun _ : ULift.{u} Unit => F) (fun _ : ULift.{u} Unit => U) (fun _ => hU) start
  let CT := stageScalarModel S C.hom t
  let FT := stageScalarModel S F.hom t
  let β := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
  let κ := Spec.map (CommRingCat.ofHom (algebraMap t.val K))
  let qC : (genericScalarModel S C.hom).left ⟶ CT.left :=
    (modelScalarCone S C.hom).π.app (op t)
  let qF : (genericScalarModel S F.hom).left ⟶ FT.left :=
    (modelScalarCone S F.hom).π.app (op t)
  let iT : CT ⟶ FT := scalarMorphism β i
  have hC : IsPullback qC (genericScalarModel S C.hom).hom CT.hom κ :=
    generic_stage_cartesian S C t
  have hF : IsPullback qF (genericScalarModel S F.hom).hom FT.hom κ :=
    generic_stage_cartesian S F t
  let D : Over (Spec (.of t.val)) := Over.mk ((V ⟨()⟩).ι ≫ FT.hom)
  let j : D ⟶ FT := Over.homMk (V ⟨()⟩).ι rfl
  let : IsAffine D.left := hV ⟨()⟩
  let : CompactSpace CT.left := by
    change CompactSpace (pullback β C.hom : Scheme.{u})
    let : QuasiCompact β :=
      inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion t.property.2).toRingHom)))
    exact compactBaseChange β C.hom
  let : QuasiSeparatedSpace CT.left := by
    change QuasiSeparatedSpace (pullback β C.hom : Scheme.{u})
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst β C.hom)
  let : LocallyOfFinitePresentation CT.hom := by
    change LocallyOfFinitePresentation (pullback.fst β C.hom)
    infer_instance
  let : LocallyOfFinitePresentation FT.hom := by
    change LocallyOfFinitePresentation (pullback.fst β F.hom)
    infer_instance
  let : LocallyOfFinitePresentation D.hom := by
    change LocallyOfFinitePresentation ((V ⟨()⟩).ι ≫ FT.hom)
    infer_instance
  let : IsOpenImmersion j.left := by
    change IsOpenImmersion (V ⟨()⟩).ι
    infer_instance
  let UK : Over (Spec (.of K)) :=
    Over.mk (U.ι ≫ (genericScalarModel S F.hom).hom)
  let e : genericScalarModel S C.hom ≅ UK :=
    openRangeIso (genericScalarModel S C.hom) (genericScalarModel S F.hom) iK
  obtain ⟨EU, hEU⟩ := exists_scalar_open_iso κ (genericScalarModel S F.hom) FT qF hF
    (V ⟨()⟩) U (hpreimage ⟨()⟩)
  let EC : genericScalarModel S C.hom ≅ genericScalarModel t.val CT.hom :=
    modelComparison κ CT (X := genericScalarModel S C.hom) qC hC
  let E : genericScalarModel t.val CT.hom ≅ genericScalarModel t.val D.hom :=
    EC.symm ≪≫ e ≪≫ EU
  have hE : E.hom.left ≫ pullback.snd κ D.hom ≫ j.left =
      pullback.snd κ CT.hom ≫ iT.left := by
    exact conjugate_triangle (underlyingIso EC) (underlyingIso EU) (underlyingIso e)
      qC (EU.hom.left ≫ pullback.snd κ D.hom) _ _ iT.left j.left iK.left U.ι qF
      (modelComparison_projection κ CT qC hC) rfl
      (Scheme.Hom.isoOpensRange_hom_ι iK.left) (generic_naturality S C F i t).symm hEU.symm
  let first : CoefficientStage t.val := ⟨t.val, t.property.1, le_rfl⟩
  obtain ⟨r, _, Er, hEr⟩ := exists_model_iso_commuting t.val t.property.1 CT D FT iT j
    E hE first
  let rS : CoefficientStage S := ⟨r.val, r.property.1, t.property.2.trans r.property.2⟩
  have htr : t ≤ rS := r.property.2
  let ρ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom)
  let CR := stageScalarModel S C.hom rS
  let FR := stageScalarModel S F.hom rS
  let DR := stageScalarModel t.val D.hom r
  let pC : CR.left ⟶ CT.left := stageScalarTransition S C.hom htr
  let pF : FR.left ⟶ FT.left := stageScalarTransition S F.hom htr
  have hCR : IsPullback pC CR.hom CT.hom ρ := stageScalarCartesian S C.hom htr
  have hFR : IsPullback pF FR.hom FT.hom ρ := stageScalarCartesian S F.hom htr
  let α : CR ≅ stageScalarModel t.val CT.hom r :=
    modelComparison ρ CT (X := CR) pC hCR
  let Efinal : CR ≅ DR := α ≪≫ Er
  let fD : DR ⟶ FR := cartesianLift ρ D FT FR pF hFR j
  let fC : CR ⟶ FR := scalarMorphism
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion rS.property.2).toRingHom)) i
  have hfinal : Efinal.hom.left ≫ pullback.snd ρ D.hom ≫ j.left = pC ≫ iT.left :=
    iso_prefix_triangle α Er pC _ _ iT.left j.left
      (modelComparison_projection ρ CT pC hCR) hEr
  refine ⟨rS, hstartt.trans htr, ?_⟩
  exact open_of_comparison ρ CT D FT CR DR FR iT j pC _ pF
    (IsPullback.of_hasPullback _ _).flip hFR fC fD
    (stage_naturality S C F i htr).symm
    (cartesianLift_projection ρ D FT FR pF hFR j) Efinal hfinal

private theorem chart_open_stage
    {K : Type u} [kComm : CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    (C F : Over (Spec (.of S)))
    [cCompact : CompactSpace C.left] [cQS : QuasiSeparatedSpace C.left]
    [fQS : QuasiSeparatedSpace F.left]
    [cFP : LocallyOfFinitePresentation C.hom] [fFP : LocallyOfFinitePresentation F.hom]
    (CK FK : Over (Spec (.of K))) (hAffine : IsAffine CK.left)
    (i : C ⟶ F) (iK : CK ⟶ FK) (hOpen : IsOpenImmersion iK.left)
    (qC : CK.left ⟶ C.left) (qF : FK.left ⟶ F.left)
    (hC : IsPullback qC CK.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF FK.hom F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hi : iK.left ≫ qF = qC ≫ i.left) (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t), IsOpenImmersion
      (scalarMorphism (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion t.property.2).toRingHom)) i).left := by
  have hData := @scalar_open_of_chart.{u} (Spec (.of S)) (Spec (.of K))
    (Spec.map (CommRingCat.ofHom (algebraMap S K))) C F CK FK hAffine
    i iK hOpen qC qF hC hF hi
  obtain ⟨hAffineScalar, hOpenScalar⟩ := hData
  exact @exists_open_stage.{u} K kComm S hS C F
    cCompact cQS fQS cFP fFP i hAffineScalar hOpenScalar start

private theorem open_stage_mono
    {K : Type u} [kComm : CommRing K] (S : Subalgebra ℤ K)
    (C F : Over (Spec (.of S))) (i : C ⟶ F)
    {t r : CoefficientStage S} (htr : t ≤ r)
    (hOpen : IsOpenImmersion (scalarMorphism (Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion t.property.2).toRingHom)) i).left) :
    IsOpenImmersion (scalarMorphism (Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion r.property.2).toRingHom)) i).left := by
  have hcart := @cartesian_map.{u} (Spec (.of t.val)) (Spec (.of r.val))
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion htr).toRingHom))
    (stageScalarModel S C.hom t) (stageScalarModel S F.hom t)
    (stageScalarModel S C.hom r) (stageScalarModel S F.hom r)
    (scalarMorphism (Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion t.property.2).toRingHom)) i)
    (stageScalarTransition S C.hom htr) (stageScalarTransition S F.hom htr)
    (@stageScalarCartesian.{u} K kComm S C.left C.hom t r htr)
    (@stageScalarCartesian.{u} K kComm S F.left F.hom t r htr)
    (scalarMorphism (Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion r.property.2).toRingHom)) i)
    (stage_naturality S C F i htr).symm
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hcart.flip hOpen

/-- Beyond one coefficient stage, the polynomial tensor chart is open over
every later stage, with its coefficient, flag and polynomial projections. -/
theorem exists_opposition_open_stage
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (r : G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG)
    (B : Type u) [bComm : CommRing B] [sB : Algebra S B]
    [bFP : Algebra.FinitePresentation S B]
    (e : K ⊗[S] B ≃ₐ[K] chartAlgebra G r)
    (F : Over (Spec (.of S)))
    [fQS : QuasiSeparatedSpace F.left] [fFP : LocallyOfFinitePresentation F.hom]
    (qF : (flagVariety G).toOver.left ⟶ F.left)
    (hF : IsPullback qF (flagVariety G).toOver.hom F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    ∃ (lower : CoefficientStage S) (_ : start ≤ lower),
    ∀ (t : CoefficientStage S) (_ : lower ≤ t),
      let sT : Algebra S t.val := (Subalgebra.inclusion t.property.2).toAlgebra
      let tower : IsScalarTower S t.val K :=
        Subalgebra.inclusion.isScalarTower_right t.property.2 K
      Nonempty (@PolynomialOpenModel.{u} S t.val K B (chartAlgebra G r)
        (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing t.val))
        kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
        sT (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra t.val K))
        sB (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e F
        (flagVariety G).toOver qF
        (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left) := by
  have hFactory := @exists_opposition_chart_map.{u} K kField kClosed kZero
    G r S hS B bComm sB e F fFP qF hF start
  obtain ⟨t, ht, hData⟩ := hFactory
  let sT : Algebra S t.val := (Subalgebra.inclusion t.property.2).toAlgebra
  let towerT : IsScalarTower S t.val K :=
    Subalgebra.inclusion.isScalarTower_right t.property.2 K
  obtain ⟨i0, qF0, hH0, hF0, hOldF0, hchart0⟩ := hData
  let H0 : Over (Spec (.of t.val)) := @polynomialModel.{u} t.val (t.val ⊗[S] B)
          (inferInstanceAs (CommRing t.val))
          (inferInstanceAs (CommRing (t.val ⊗[S] B)))
          (inferInstanceAs (Algebra t.val (t.val ⊗[S] B)))
  let F0 := stageScalarModel S F.hom t
  let qH0 : (affineVariety K (Polynomial (chartAlgebra G r))).toOver.left ⟶ H0.left :=
    Spec.map (@CommRingCat.ofHom (Polynomial (t.val ⊗[S] B))
      (Polynomial (chartAlgebra G r))
      (inferInstanceAs (CommRing (Polynomial (t.val ⊗[S] B))))
      (inferInstanceAs (CommRing (Polynomial (chartAlgebra G r))))
      (Polynomial.mapRingHom
      (@FrobeniusSplitting.RetainedCharacter.scalarMap S t.val K B (chartAlgebra G r)
        (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing t.val))
        kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
        sT (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra t.val K))
        sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerT e)))
  have hPolynomial := @polynomial_model_properties.{u}
    t.val (t.val ⊗[S] B) (inferInstanceAs (CommRing t.val))
    (inferInstanceAs (CommRing (t.val ⊗[S] B)))
    (inferInstanceAs (Algebra t.val (t.val ⊗[S] B)))
    (inferInstanceAs (Algebra.FinitePresentation t.val (t.val ⊗[S] B)))
  obtain ⟨hCompact, hQS, hFP⟩ := hPolynomial
  let : CompactSpace H0.left := hCompact
  let : QuasiSeparatedSpace H0.left := hQS
  let : LocallyOfFinitePresentation H0.hom := hFP
  let : QuasiSeparatedSpace F0.left := by
    change QuasiSeparatedSpace (pullback _ F.hom : Scheme.{u})
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd _ F.hom)
  let : LocallyOfFinitePresentation F0.hom := by
    change LocallyOfFinitePresentation (pullback.fst _ F.hom)
    infer_instance
  have hXAffine : IsAffine (affineVariety K (Polynomial (chartAlgebra G r))).toOver.left := by
    change IsAffine (Spec (.of (Polynomial (chartAlgebra G r))))
    infer_instance
  have hStage := @chart_open_stage.{u} K kField.toCommRing t.val t.property.1
    H0 F0 inferInstance inferInstance inferInstance inferInstance inferInstance
    (affineVariety K (Polynomial (chartAlgebra G r))).toOver (flagVariety G).toOver
    hXAffine i0 (@oppositionPolynomialMap.{u} K kField kClosed kZero G r)
    (@oppositionPolynomialMap_open.{u} K kField kClosed kZero G r)
    qH0 qF0 hH0 hF0 hchart0 ⟨t.val, t.property.1, le_rfl⟩
  obtain ⟨v, _, hiv⟩ := hStage
  let lower : CoefficientStage S :=
    ⟨v.val, v.property.1, t.property.2.trans v.property.2⟩
  refine ⟨lower, ht.trans v.property.2, ?_⟩
  intro u hlu
  let w : CoefficientStage t.val :=
    ⟨u.val, u.property.1, v.property.2.trans hlu⟩
  have hvw : v ≤ w := hlu
  have hi1 := @open_stage_mono.{u} K kField.toCommRing t.val H0 F0 i0 v w hvw hiv
  let β := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion w.property.2).toRingHom)
  let H1 := stageScalarModel t.val H0.hom w
  let F1 := stageScalarModel t.val F0.hom w
  let pH := pullback.snd β H0.hom
  let pF := pullback.snd β F0.hom
  let i1 : H1 ⟶ F1 := scalarMorphism β i0
  let α := modelComparison (Spec.map (CommRingCat.ofHom (algebraMap t.val K)))
    H0 (X := (affineVariety K (Polynomial (chartAlgebra G r))).toOver) qH0 hH0
  let δ := modelComparison (Spec.map (CommRingCat.ofHom (algebraMap t.val K)))
    F0 (X := (flagVariety G).toOver) qF0 hF0
  let qH1 := α.hom.left ≫ (modelScalarCone t.val H0.hom).π.app (op w)
  let qF1 := δ.hom.left ≫ (modelScalarCone t.val F0.hom).π.app (op w)
  have hH1 := @overIso_modelStage_cartesian.{u} K kField.toCommRing t.val
    H0.left H0.hom w (affineVariety K (Polynomial (chartAlgebra G r))).toOver α
  have hF1 := @overIso_modelStage_cartesian.{u} K kField.toCommRing t.val
    F0.left F0.hom w (flagVariety G).toOver δ
  have hOldH1 : qH1 ≫ pH = qH0 := composite_projection α.hom.left _ _ _ qH0
    (scalarLeg_snd t.val H0.hom w) (modelComparison_projection _ H0 qH0 hH0)
  have hOldF1 : qF1 ≫ pF = qF0 := composite_projection δ.hom.left _ _ _ qF0
    (scalarLeg_snd t.val F0.hom w) (modelComparison_projection _ F0 qF0 hF0)
  have hchart1 := @naturality_square.{u}
    (Spec (.of t.val)) (Spec (.of w.val)) (Spec (.of K)) β
    (Spec.map (CommRingCat.ofHom (algebraMap w.val K)))
    H0 F0 H1 F1 (affineVariety K (Polynomial (chartAlgebra G r))).toOver
    (flagVariety G).toOver i0 i1
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r)
    pH pF qH0 qF0 qH1 qF1 (IsPullback.of_hasPullback _ F0.hom).flip
    (scalarMorphism_projection β i0) hchart0 hOldH1 hOldF1 hH1.w hF1.w
  have hScalar : β ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom) =
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion u.property.2).toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  have hBaseAll := @exists_scalar_polynomial_square.{u}
    S t.val B (t.val ⊗[S] B) (inferInstanceAs (CommRing S))
    (inferInstanceAs (CommRing t.val)) bComm (inferInstanceAs (CommRing (t.val ⊗[S] B)))
    sT sB (inferInstanceAs (Algebra t.val (t.val ⊗[S] B)))
    (AlgEquiv.refl : t.val ⊗[S] B ≃ₐ[t.val] t.val ⊗[S] B)
  obtain ⟨_, _, _, hBase⟩ := hBaseAll
  have hCR := (IsPullback.of_hasPullback β H0.hom).flip.paste_horiz hBase
  rw [hScalar] at hCR
  let projection : F1.left ⟶ F.left := pF ≫ pullback.snd
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) F.hom
  have hFR := (IsPullback.of_hasPullback β F0.hom).flip.paste_horiz
    (IsPullback.of_hasPullback
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) F.hom).flip
  rw [hScalar] at hFR
  have hProjection : qF1 ≫ projection = qF :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ pullback.snd _ F.hom) hOldF1).trans hOldF0)
  let l0 : H0.left ⟶ Spec (.of (Polynomial B)) := Spec.map
    (@CommRingCat.ofHom (Polynomial B) (Polynomial (t.val ⊗[S] B))
      (inferInstanceAs (CommRing (Polynomial B)))
      (inferInstanceAs (CommRing (Polynomial (t.val ⊗[S] B))))
      (Polynomial.mapRingHom
    ((AlgEquiv.refl : t.val ⊗[S] B ≃ₐ[t.val] t.val ⊗[S] B).toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[S] t.val ⊗[S] B).toRingHom)))
  have hOriginal := @polynomial_scalar_projection.{u}
    S t.val K B (chartAlgebra G r) (inferInstanceAs (CommRing S))
    (inferInstanceAs (CommRing t.val)) kField.toCommRing bComm
    (inferInstanceAs (CommRing (chartAlgebra G r))) sT
    (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra t.val K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerT e
    H1.left qH1 pH hOldH1
  let sR : Algebra S u.val := (Subalgebra.inclusion u.property.2).toAlgebra
  let towerR : IsScalarTower S u.val K :=
    Subalgebra.inclusion.isScalarTower_right u.property.2 K
  have hLiteral := @exists_polynomial_tensor_chart.{u}
    S u.val K B (chartAlgebra G r) (inferInstanceAs (CommRing S))
    (inferInstanceAs (CommRing u.val)) kField.toCommRing bComm
    (inferInstanceAs (CommRing (chartAlgebra G r))) sR
    (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra u.val K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR e
    H1 F1 (pH ≫ l0) hCR (flagVariety G).toOver.left
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left
    qH1 qF1 i1 hOriginal hH1.w hchart1.symm
  obtain ⟨i, hH, hi, hOpen⟩ := hLiteral
  exact ⟨@PolynomialOpenModel.mk.{u} S u.val K B (chartAlgebra G r)
    (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing u.val))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra u.val K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR e F
    (flagVariety G).toOver qF
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left
    F1 projection hFR qF1 hF1 hProjection i (hOpen hi1) hH hi⟩

end SchubertGeometry.DeterminantSection
