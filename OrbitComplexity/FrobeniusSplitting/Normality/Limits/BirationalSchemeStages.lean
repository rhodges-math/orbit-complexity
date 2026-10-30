import OrbitComplexity.FrobeniusSplitting.Normality.Limits.AffineOpenStages
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.PointedIsoStages
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.PointedScalarCells
import Batteries.Tactic.OpenPrivate

/-! # Pointed birational endpoints at coefficient stages

A pointed affine partial isomorphism of the generic endpoint descends to a
coefficient stage. Every subsequent irreducible field fibre of the same
source and target is birational through its prescribed endpoint.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace FrobeniusSplitting

universe u

open private model_scalar_original from
  OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian

private def scalarEndpoint {B T : Scheme.{u}} (κ : T ⟶ B)
    {C F : Over B} (e : C ⟶ F) :
    Over.mk (pullback.fst κ C.hom) ⟶ Over.mk (pullback.fst κ F.hom) :=
  Over.homMk (pullback.map κ C.hom κ F.hom (𝟙 T) e.left (𝟙 B)
    (by simp) (by simp)) (by simp)

private theorem scalarEndpoint_original {B T : Scheme.{u}} (κ : T ⟶ B)
    {C F : Over B} (e : C ⟶ F) :
    (scalarEndpoint κ e).left ≫ pullback.snd κ F.hom =
      pullback.snd κ C.hom ≫ e.left := by
  change (pullback.map κ C.hom κ F.hom (𝟙 T) e.left (𝟙 B) (by simp) (by simp)) ≫
    pullback.snd κ F.hom = _
  exact pullback.lift_snd _ _ _

private theorem endpoint_from_projections {B R T : Scheme.{u}}
    (ρ : R ⟶ B) (β : T ⟶ R)
    (C F : Over B) (CR FR : Over R) (CT FT : Over T)
    (qCR : CR.left ⟶ C.left) (qFR : FR.left ⟶ F.left)
    (hFR : IsPullback qFR FR.hom F.hom ρ)
    (e : C ⟶ F) (eR : CR ⟶ FR)
    (heR : eR.left ≫ qFR = qCR ≫ e.left)
    (qCT : CT.left ⟶ C.left) (qFT : FT.left ⟶ F.left)
    (qC : CT.left ⟶ CR.left) (qF : FT.left ⟶ FR.left)
    (hc : qC ≫ qCR = qCT) (hf : qF ≫ qFR = qFT)
    (hcb : qC ≫ CR.hom = CT.hom ≫ β)
    (hfb : qF ≫ FR.hom = FT.hom ≫ β)
    (eT : CT ⟶ FT) (heT : eT.left ≫ qFT = qCT ≫ e.left) :
    eT.left ≫ qF = qC ≫ eR.left := by
  apply hFR.hom_ext
  · calc
      (eT.left ≫ qF) ≫ qFR = eT.left ≫ qFT :=
        (Category.assoc _ _ _).trans (congrArg (fun a => eT.left ≫ a) hf)
      _ = qCT ≫ e.left := heT
      _ = (qC ≫ qCR) ≫ e.left := congrArg (fun a => a ≫ e.left) hc.symm
      _ = qC ≫ (eR.left ≫ qFR) :=
        (Category.assoc _ _ _).trans (congrArg (fun a => qC ≫ a) heR.symm)
      _ = (qC ≫ eR.left) ≫ qFR := (Category.assoc _ _ _).symm
  · calc
      (eT.left ≫ qF) ≫ FR.hom = eT.left ≫ (FT.hom ≫ β) :=
        (Category.assoc _ _ _).trans (congrArg (fun a => eT.left ≫ a) hfb)
      _ = CT.hom ≫ β := (Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ β) eT.w)
      _ = qC ≫ CR.hom := hcb.symm
      _ = (qC ≫ eR.left) ≫ FR.hom := by rw [Category.assoc, eR.w]

private theorem endpoint_composite {A B C D E F : Scheme.{u}}
    (u : A ⟶ B) (v : B ⟶ C) (u' : D ⟶ E) (v' : E ⟶ F)
    (f : A ⟶ D) (g : B ⟶ E) (h : C ⟶ F)
    (hf : f ≫ u' = u ≫ g) (hg : g ≫ v' = v ≫ h) :
    f ≫ (u' ≫ v') = (u ≫ v) ≫ h := by
  calc
    f ≫ (u' ≫ v') = (f ≫ u') ≫ v' := (Category.assoc _ _ _).symm
    _ = (u ≫ g) ≫ v' := congrArg (fun a => a ≫ v') hf
    _ = u ≫ (v ≫ h) := (Category.assoc _ _ _).trans
      (congrArg (fun a => u ≫ a) hg)
    _ = (u ≫ v) ≫ h := (Category.assoc _ _ _).symm

private theorem coefficient_composite {K : Type u} [CommRing K]
    (S R T : Subalgebra ℤ K) (hSR : S ≤ R) (hRT : R ≤ T) :
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hSR).toRingHom) =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hSR.trans hRT)).toRingHom) := by
  rw [← Spec.map_comp]
  rfl

private theorem model_open_comparison {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    (i : CoefficientStage S) (U : (genericScalarModel S a).left.Opens)
    (V : (stageScalarModel S a i).left.Opens)
    (hU : (modelScalarCone S a).π.app (op i) ⁻¹ᵁ V = U) :
    ∃ q : (genericScalarModel S a).left ⟶ (stageScalarModel S a i).left,
      IsPullback q (genericScalarModel S a).hom (stageScalarModel S a i).hom
        (Spec.map (CommRingCat.ofHom (algebraMap i.val K))) ∧
      q ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) a =
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) a ∧
      q ⁻¹ᵁ V = U := by
  exact ⟨(modelScalarCone S a).π.app (op i), modelScalarCone_cartesian S a i,
    model_scalar_original S a i, hU⟩

set_option maxHeartbeats 100000 in
/-- A pointed affine partial isomorphism of a generic endpoint extends to one
coefficient stage above any prescribed stage. On every later field fibre with
irreducible source and target, the same endpoint is birational; arbitrary
Cartesian comparisons with the original source and target are retained. -/
theorem exists_birational_scalar_stage {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) (C F : Over (Spec (.of S)))
    [QuasiSeparatedSpace C.left] [QuasiSeparatedSpace F.left]
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation F.hom]
    (e : C ⟶ F)
    (eK : genericScalarModel S C.hom ⟶ genericScalarModel S F.hom)
    (heK : eK.left ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) F.hom =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) C.hom ≫ e.left)
    (U : (genericScalarModel S C.hom).left.Opens) (hU : IsAffineOpen U)
    (V : (genericScalarModel S F.hom).left.Opens) (hV : IsAffineOpen V)
    (E : Over.mk (U.ι ≫ (genericScalarModel S C.hom).hom) ≅
      Over.mk (V.ι ≫ (genericScalarModel S F.hom).hom))
    (hE : E.hom.left ≫ V.ι = U.ι ≫ eK.left)
    (s : Spec (.of K) ⟶ V.toScheme)
    (hs : s ≫ (V.ι ≫ (genericScalarModel S F.hom).hom) = 𝟙 _)
    (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t),
      ∀ (L : Type u) [Field L] [Algebra t.val L]
        (CL FL : Over (Spec (.of L)))
        [IrreducibleSpace CL.left] [IrreducibleSpace FL.left]
        (qC : CL.left ⟶ C.left) (qF : FL.left ⟶ F.left)
        (_hC : IsPullback qC CL.hom C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val L)) ≫
            Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)))
        (_hF : IsPullback qF FL.hom F.hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val L)) ≫
            Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)))
        (eL : CL ⟶ FL) (_heL : eL.left ≫ qF = qC ≫ e.left),
        Scheme.BirationalOver eL.left (𝟙 FL.left) := by
  classical
  let P : ULift.{u} Bool → Over (Spec (.of S)) := fun b => if b.down then F else C
  let PU : ∀ b, (genericScalarModel S (P b).hom).left.Opens := fun b => by
    rcases b with ⟨b⟩
    cases b
    · exact U
    · exact V
  have hPU (b) : IsAffineOpen (PU b) := by
    rcases b with ⟨b⟩
    cases b
    · exact hU
    · exact hV
  let : ∀ b, QuasiSeparatedSpace (P b).left := fun b => by
    rcases b with ⟨b⟩
    cases b
    · exact inferInstanceAs (QuasiSeparatedSpace C.left)
    · exact inferInstanceAs (QuasiSeparatedSpace F.left)
  obtain ⟨r, hstart, O, hO, hpre⟩ := exists_affine_opens_stage S hS P PU hPU start
  let CR := stageScalarModel S C.hom r
  let FR := stageScalarModel S F.hom r
  let ρ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom)
  let κ := Spec.map (CommRingCat.ofHom (algebraMap r.val K))
  let qCR : CR.left ⟶ C.left := pullback.snd ρ C.hom
  let qFR : FR.left ⟶ F.left := pullback.snd ρ F.hom
  let eR : CR ⟶ FR := scalarEndpoint ρ e
  have heR : eR.left ≫ qFR = qCR ≫ e.left := scalarEndpoint_original ρ e
  have hCR : IsPullback qCR CR.hom C.hom ρ :=
    (IsPullback.of_hasPullback ρ C.hom).flip
  have hFR : IsPullback qFR FR.hom F.hom ρ :=
    (IsPullback.of_hasPullback ρ F.hom).flip
  let UR : CR.left.Opens := O ⟨false⟩
  let VR : FR.left.Opens := O ⟨true⟩
  obtain ⟨qCK, hCK, hCKold, hCKpre⟩ :=
    model_open_comparison S C.hom r U UR (hpre ⟨false⟩)
  obtain ⟨qFK, hFK, hFKold, hFKpre⟩ :=
    model_open_comparison S F.hom r V VR (hpre ⟨true⟩)
  have heKR : eK.left ≫ qFK = qCK ≫ eR.left :=
    endpoint_from_projections ρ κ C F CR FR _ _ qCR qFR hFR e eR heR _ _ qCK qFK
      hCKold hFKold
      hCK.w hFK.w eK heK
  obtain ⟨ER, sR, hsR, hER⟩ := transport_pointed_open κ _ _ CR FR qCK qFK hCK hFK
    eR eK heKR UR VR U V hCKpre hFKpre E hE s hs
  let : LocallyOfFinitePresentation CR.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst ρ C.hom))
  let : LocallyOfFinitePresentation FR.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst ρ F.hom))
  let first : CoefficientStage r.val := ⟨r.val, r.property.1, le_rfl⟩
  obtain ⟨v, _, Ev, sv, hsv, hEv⟩ := exists_pointed_iso_stage r.val r.property.1 CR FR eR
    UR (hO ⟨false⟩) VR (hO ⟨true⟩) ER hER sR hsR first
  let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion v.property.2).toRingHom)
  let DC := stageScalarModel r.val CR.hom v
  let DF := stageScalarModel r.val FR.hom v
  let qDC : DC.left ⟶ CR.left := pullback.snd τ CR.hom
  let qDF : DF.left ⟶ FR.left := pullback.snd τ FR.hom
  let eD : DC ⟶ DF := scalarEndpoint τ eR
  have heD : eD.left ≫ qDF = qDC ≫ eR.left := scalarEndpoint_original τ eR
  have hDC : IsPullback qDC DC.hom CR.hom τ :=
    (IsPullback.of_hasPullback τ CR.hom).flip
  have hDF : IsPullback qDF DF.hom FR.hom τ :=
    (IsPullback.of_hasPullback τ FR.hom).flip
  obtain ⟨W, c, j, hc, hj, hcell, k, hk⟩ :=
    exists_pointed_scalar_cell τ CR FR eR UR VR Ev hEv sv hsv
      DC DF qDC qDF hDC hDF eD heD
  let : IsOpenImmersion c.left := hc
  let : IsOpenImmersion j.left := hj
  let t : CoefficientStage S :=
    ⟨v.val, v.property.1, r.property.2.trans v.property.2⟩
  have hrt : r ≤ t := v.property.2
  have hcoeff : τ ≫ ρ =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom) :=
    coefficient_composite S r.val v.val r.property.2 v.property.2
  have hDC0 : IsPullback (qDC ≫ qCR) DC.hom C.hom (τ ≫ ρ) :=
    hDC.paste_horiz hCR
  have hDF0 : IsPullback (qDF ≫ qFR) DF.hom F.hom (τ ≫ ρ) :=
    hDF.paste_horiz hFR
  have heD0 : eD.left ≫ (qDF ≫ qFR) = (qDC ≫ qCR) ≫ e.left :=
    endpoint_composite qDC qCR qDF qFR eD.left eR.left e.left heD heR
  refine ⟨t, hstart.trans hrt, ?_⟩
  intro L _ _ CL FL _ _ qCL qFL hCL hFL eL heL
  let β := Spec.map (CommRingCat.ofHom (algebraMap t.val L))
  have hCL0 : IsPullback qCL CL.hom C.hom (β ≫ (τ ≫ ρ)) := by
    rw [hcoeff]
    exact hCL
  have hFL0 : IsPullback qFL FL.hom F.hom (β ≫ (τ ≫ ρ)) := by
    rw [hcoeff]
    exact hFL
  obtain ⟨qCD, qFD, hCD, hFD, heLD, _, _⟩ :=
    factor_endpoint_square (τ ≫ ρ) β C F DC DF CL FL
      (qDC ≫ qCR) (qDF ≫ qFR) hDC0 hDF0 e eD heD0
      qCL qFL hCL0 hFL0 eL heL
  exact pointed_cell_birational W DC DF c j eD hcell k hk
    CL FL β qCD qFD hCD hFD eL heLD

end FrobeniusSplitting
