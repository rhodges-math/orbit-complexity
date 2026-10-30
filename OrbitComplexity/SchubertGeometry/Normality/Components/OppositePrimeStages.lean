import OrbitComplexity.SchubertGeometry.Normality.SchubertImageStages
import OrbitComplexity.SchubertGeometry.Normality.BottSamelson.ProperWordFibres
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares
import OrbitComplexity.FrobeniusSplitting.Normality.Components.IntegralImagePrimes
import OrbitComplexity.FrobeniusSplitting.Normality.SchemeFiniteness
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Prime ideals of opposite Schubert images over coefficient stages -/

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace SchubertGeometry

universe u

open ReductiveGroups FrobeniusSplitting

open private modelComparison from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares
open private iso_old_base from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.PointedIsoStages

private theorem coefficient_comp {K : Type u} [CommRing K]
    {S T U R : Subalgebra ℤ K} (hST : S ≤ T) (hTU : T ≤ U)
    (hUR : U ≤ R) (hSR : S ≤ R) {L : Type u} [CommRing L] (a : R →+* L) :
    a.comp (Subalgebra.inclusion hSR).toRingHom =
      ((a.comp (Subalgebra.inclusion hUR).toRingHom).comp
        (Subalgebra.inclusion hTU).toRingHom).comp
          (Subalgebra.inclusion hST).toRingHom := by
  ext x
  rfl

private theorem coefficient_spec_comp {K : Type u} [CommRing K]
    {S T U R : Subalgebra ℤ K} (hST : S ≤ T) (hTU : T ≤ U)
    (hUR : U ≤ R) (hSR : S ≤ R) {L : Type u} [CommRing L] (a : R →+* L) :
    Spec.map (CommRingCat.ofHom (a.comp (Subalgebra.inclusion hSR).toRingHom)) =
      (Spec.map (CommRingCat.ofHom (a.comp (Subalgebra.inclusion hUR).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hTU).toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom) := by
  have h := congrArg (fun f : S →+* L => Spec.map (CommRingCat.ofHom f))
    (coefficient_comp hST hTU hUR hSR a)
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp] using h

private theorem integral_fibre_of_iso
    {B T U V : Scheme.{u}} (s : T ⟶ B) (κ : U ⟶ T) (b : V ⟶ U)
    (C : Over B) (D C₀ : Over T) (D₁ C₁ : Over U)
    (q₀ : C₀.left ⟶ C.left) (qD : D₁.left ⟶ D.left)
    (qC : C₁.left ⟶ C₀.left)
    (h₀ : IsPullback q₀ C₀.hom C.hom s)
    (hD : IsPullback qD D₁.hom D.hom κ)
    (hC : IsPullback qC C₁.hom C₀.hom κ)
    (E : D₁ ≅ C₁) (X : Over V) (qX : X.left ⟶ C.left) (a : V ⟶ B)
    (ha : a = (b ≫ κ) ≫ s) (hX : IsPullback qX X.hom C.hom a)
    [IsIntegral (pullback D.hom (b ≫ κ))] : IsIntegral X.left := by
  have hD' := (IsPullback.of_hasPullback D₁.hom b).paste_horiz hD
  have hC' := ((IsPullback.of_hasPullback C₁.hom b).paste_horiz hC).paste_horiz h₀
  have hX' : IsPullback qX X.hom C.hom ((b ≫ κ) ≫ s) := ha ▸ hX
  let E' := (Over.forget V).mapIso ((Over.pullback b).mapIso E)
  let H : X.left ≅ pullback D.hom (b ≫ κ) :=
    hX'.isoPullback ≪≫ hC'.isoPullback.symm ≪≫ E'.symm ≪≫ hD'.isoPullback
  exact IsIntegral.of_isIso H.inv

private theorem noetherian_fibre
    {B : Scheme.{u}} {L : Type u} [Field L]
    (C : Over B) [QuasiCompact C.hom] [LocallyOfFiniteType C.hom]
    (a : Spec (.of L) ⟶ B) (X : Over (Spec (.of L)))
    (qX : X.left ⟶ C.left) (hX : IsPullback qX X.hom C.hom a) :
    TopologicalSpace.NoetherianSpace X.left := by
  have : IsNoetherian (pullback C.hom a) :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := inferInstance }
  exact (TopologicalSpace.noetherianSpace_iff_of_homeomorph hX.isoPullback.hom.homeomorph).mpr
    (inferInstance : TopologicalSpace.NoetherianSpace (pullback C.hom a : Scheme.{u}))

private theorem word_models_isomorphic {K : Type u} [hK : Field K]
    [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (S : Subalgebra ℤ K) (C : Over (Spec (.of S)))
    (qC : (bsdhVariety G word).toOver.left ⟶ C.left)
    (hC : IsPullback qC (bsdhVariety G word).toOver.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (T : Subalgebra ℤ K) (hT : T.FG) (hST : S ≤ T)
    (Y : Scheme.{u}) (base : Y ⟶ Spec (.of T))
    (m : bsdhScheme G word ⟶ Y)
    (hY : IsPullback m (bsdhToSpec G word) base
      (Spec.map (CommRingCat.ofHom (algebraMap T K)))) :
    Nonempty (genericScalarModel T base ≅
      genericScalarModel T (stageScalarModel S C.hom ⟨T, hT, hST⟩).hom) := by
  have EC := @modelComparison (Spec (.of S)) (Spec (.of K))
    (Spec.map (CommRingCat.ofHom (algebraMap S K))) C
    (bsdhVariety G word).toOver qC hC
  have hCt := @overIso_modelStage_cartesian K hK.toCommRing S C.left C.hom
    ⟨T, hT, hST⟩ (bsdhVariety G word).toOver EC
  have EY := @modelComparison (Spec (.of T)) (Spec (.of K))
    (Spec.map (CommRingCat.ofHom (algebraMap T K))) (Over.mk base)
    (bsdhVariety G word).toOver m hY
  have EStage := @modelComparison (Spec (.of T)) (Spec (.of K))
    (Spec.map (CommRingCat.ofHom (algebraMap T K)))
    (stageScalarModel S C.hom ⟨T, hT, hST⟩) (bsdhVariety G word).toOver
    (EC.hom.left ≫ (modelScalarCone S C.hom).π.app (op ⟨T, hT, hST⟩)) hCt
  exact ⟨EY.symm ≪≫ EStage⟩

/-- Opposite Schubert field fibres are integral and their image ideals on every
affine open are prime or the unit ideal after one coefficient extension. -/
theorem exists_opposite_prime_stage {K : Type u} [hK : Field K]
    [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (S : Subalgebra ℤ K) (hS : S.FG)
    (C D : Over (Spec (.of S)))
    [hCFP : LocallyOfFinitePresentation C.hom]
    [hDFP : LocallyOfFinitePresentation D.hom]
    [hCCompact : CompactSpace C.left]
    [hDCompact : CompactSpace D.left] (e : C ⟶ D) [hEQC : QuasiCompact e.left]
    (qC : (bsdhVariety G word).toOver.left ⟶ C.left)
    (qD : (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toOver.left ⟶ D.left)
    (hC : IsPullback qC (bsdhVariety G word).toOver.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toOver.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hsquare : qC ≫ e.left = (bsdhOppositeSchubertMap G word hred).left ≫ qD)
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ start ≤ R ∧ ∃ hSR : S ≤ R,
      ∀ (L : Type u) [Field L] [Algebra R L]
        (XL YL : Over (Spec (.of L))) (fL : XL ⟶ YL) [QuasiCompact fL.left]
        (qXL : XL.left ⟶ C.left) (qYL : YL.left ⟶ D.left)
        (_hXL : IsPullback qXL XL.hom C.hom
          (Spec.map (CommRingCat.ofHom
            ((algebraMap R L).comp (Subalgebra.inclusion hSR).toRingHom))))
        (_hYL : IsPullback qYL YL.hom D.hom
          (Spec.map (CommRingCat.ofHom
            ((algebraMap R L).comp (Subalgebra.inclusion hSR).toRingHom))))
        (_hfL : fL.left ≫ qYL = qXL ≫ e.left),
        IsIntegral YL.left ∧
          ∀ (Z : Scheme.{u}) (j : YL.left ⟶ Z) (U : Z.affineOpens),
            j.ker.ideal U = ⊤ ∨ (j.ker.ideal U).IsPrime := by
  have hSFinite : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
  have hCprops := @finiteType_int_scheme_properties S (inferInstance : CommRing S)
    hSFinite C.left hCCompact C.hom hCFP
  have hCQC : QuasiCompact C.hom := hCprops.2.1
  have hCType : LocallyOfFiniteType C.hom := inferInstance
  obtain ⟨T, hsupT, hT, Y, base, m, hproper, hsmooth, _hconnected, hgood, hfibres⟩ :=
    @exists_integral_bsdh_model K hK hAlg hChar G word (S ⊔ start) (hS.sup hstart)
  have hST : S ≤ T := le_sup_left.trans hsupT
  have hstartT : start ≤ T := le_sup_right.trans hsupT
  have hTFinite : Algebra.FiniteType ℤ T := (Subalgebra.fg_iff_finiteType T).mp hT
  have hTNoeth : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing ℤ T
  have hYProper : IsProper base := hproper
  have hYSmooth : Smooth base := hsmooth
  have hYCompact : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace base
  have hYFP : LocallyOfFinitePresentation base := inferInstance
  have hYprops := @finiteType_int_scheme_properties T (inferInstance : CommRing T)
    hTFinite Y hYCompact base hYFP
  have hYNoeth : IsNoetherian Y := hYprops.1
  have hYQS : QuasiSeparatedSpace Y := inferInstance
  have hC₀Compact : CompactSpace (stageScalarModel S C.hom ⟨T, hT, hST⟩).left := by
    change CompactSpace (pullback (Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion hST).toRingHom)) C.hom : Scheme.{u})
    infer_instance
  have hC₀Loc : IsLocallyNoetherian (stageScalarModel S C.hom ⟨T, hT, hST⟩).left := by
    change IsLocallyNoetherian (pullback (Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion hST).toRingHom)) C.hom : Scheme.{u})
    infer_instance
  have hC₀QS : QuasiSeparatedSpace (stageScalarModel S C.hom ⟨T, hT, hST⟩).left :=
    inferInstance
  have hC₀FP : LocallyOfFinitePresentation
      (stageScalarModel S C.hom ⟨T, hT, hST⟩).hom := by
    change LocallyOfFinitePresentation (pullback.fst
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom)) C.hom)
    infer_instance
  have hFType : LocallyOfFiniteType (𝟙 (Spec (.of T))) := inferInstance
  obtain ⟨E⟩ := @word_models_isomorphic K hK hAlg hChar G word S C qC hC
    T hT hST Y base m hgood
  have hE := @iso_old_base (Spec (.of T)) (Spec (.of K))
    (Spec.map (CommRingCat.ofHom (algebraMap T K)))
    Y (stageScalarModel S C.hom ⟨T, hT, hST⟩).left
    base (stageScalarModel S C.hom ⟨T, hT, hST⟩).hom
    (genericScalarModel T base)
    (genericScalarModel T (stageScalarModel S C.hom ⟨T, hT, hST⟩).hom) E
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap T K))) base)
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap T K)))
      (stageScalarModel S C.hom ⟨T, hT, hST⟩).hom)
    (pullback.condition (f := Spec.map (CommRingCat.ofHom (algebraMap T K)))
      (g := base)).symm
    (pullback.condition (f := Spec.map (CommRingCat.ofHom (algebraMap T K)))
      (g := (stageScalarModel S C.hom ⟨T, hT, hST⟩).hom)).symm
  obtain ⟨t, _hstartt, Et, _hEt⟩ := @exists_model_iso_commuting K hK.toCommRing T hT
    (Over.mk base) (stageScalarModel S C.hom ⟨T, hT, hST⟩)
    (Over.mk (𝟙 (Spec (.of T)))) hYCompact hYQS hC₀Compact hC₀QS hYFP hC₀FP hFType
    (Over.homMk base (Category.comp_id base))
    (Over.homMk (stageScalarModel S C.hom ⟨T, hT, hST⟩).hom
      (Category.comp_id (stageScalarModel S C.hom ⟨T, hT, hST⟩).hom)) E hE
    ⟨T, hT, le_rfl⟩
  obtain ⟨R, hR, htR, hSR, hfields⟩ :=
    @exists_opposite_kernel_stage K hK hAlg hChar G word hred S hS C D hCFP hDFP
      hDCompact e hEQC qC qD hC hD hsquare t.val t.property.1
  refine ⟨R, hR, (hstartT.trans t.property.2).trans htR, hSR, ?_⟩
  intro L hL hRL XL YL fL hFQC qXL qYL hXL hYL hfL
  have hXLNoeth : TopologicalSpace.NoetherianSpace XL.left :=
    @noetherian_fibre (Spec (.of S)) L hL C hCQC hCType
      (Spec.map (CommRingCat.ofHom
        ((algebraMap R L).comp (Subalgebra.inclusion hSR).toRingHom))) XL qXL hXL
  have hgoodL := @hfibres L hL
    (Spec.map (CommRingCat.ofHom
      ((algebraMap R L).comp (Subalgebra.inclusion htR).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
  have hXLIntegral : IsIntegral XL.left :=
    @integral_fibre_of_iso (Spec (.of S)) (Spec (.of T)) (Spec (.of t.val))
      (Spec (.of L))
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom))
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
      (Spec.map (CommRingCat.ofHom
        ((algebraMap R L).comp (Subalgebra.inclusion htR).toRingHom)))
      C (Over.mk base) (stageScalarModel S C.hom ⟨T, hT, hST⟩)
      (stageScalarModel T base t)
      (stageScalarModel T (stageScalarModel S C.hom ⟨T, hT, hST⟩).hom t)
      (pullback.snd (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion hST).toRingHom)) C.hom)
      (pullback.snd (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion t.property.2).toRingHom)) base)
      (pullback.snd (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion t.property.2).toRingHom))
        (stageScalarModel S C.hom ⟨T, hT, hST⟩).hom)
      (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion hST).toRingHom)) C.hom).flip
      (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion t.property.2).toRingHom)) base).flip
      (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion t.property.2).toRingHom))
        (stageScalarModel S C.hom ⟨T, hT, hST⟩).hom).flip Et XL qXL
      (Spec.map (CommRingCat.ofHom
        ((algebraMap R L).comp (Subalgebra.inclusion hSR).toRingHom)))
      (coefficient_spec_comp hST t.property.2 htR hSR (algebraMap R L)) hXL
      hgoodL.2.2.1
  have hfieldsL := @hfields L hL hRL XL YL fL hFQC qXL qYL hXL hYL hfL
  refine ⟨@integral_of_scheme_dominant XL.left YL.left hXLIntegral
    fL.left hFQC hfieldsL.1, ?_⟩
  intro Z j U
  have hkernel := hfieldsL.2 Z j
  have hcomposite : QuasiCompact (fL.left ≫ j) := inferInstance
  exact @image_ideal_top_or_prime XL.left YL.left Z hXLIntegral fL.left j
    hcomposite hkernel U



end SchubertGeometry
