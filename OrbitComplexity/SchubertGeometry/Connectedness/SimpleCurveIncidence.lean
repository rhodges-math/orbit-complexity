import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.AppendCellModels
import OrbitComplexity.SchubertGeometry.Parabolics.CurveFibre
import OrbitComplexity.SchubertGeometry.Normality.Curves.ClosedCurveComparison
import OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange
import OrbitComplexity.SchubertGeometry.Connectedness.ProjectiveCurveRetention
import OrbitComplexity.SchubertGeometry.Connectedness.ScalarArrowSquares

set_option autoImplicit false

/-! # Simple-curve comparisons with the specified partial-flag fibre

The translated simple-curve square constructs its coefficient comparison
with the specified fibre. Its complete-flag and coefficient projections are
both preserved.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open FrobeniusSplitting GroupActions Opposite

namespace SchubertGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem bind_witness {A : Type*} {P : A → Prop} {Q : Prop}
    (h : ∃ a, P a) (next : ∀ a, P a → Q) : Q := by
  obtain ⟨a, ha⟩ := h
  exact next a ha

private theorem fibre_coefficient_square {T : Type*} [Category T] [HasPullbacks T]
    {X F Q K B : T} (c : X ⟶ F) (a : X ⟶ K) (π : F ⟶ Q)
    (point : K ⟶ Q) (b : B ⟶ Q) (κ : K ⟶ B)
    (h : IsPullback c a π point) (hp : point = κ ≫ b) :
    ∃ q : X ⟶ pullback π b,
      IsPullback q a (pullback.snd π b) κ ∧
      q ≫ pullback.fst π b = c ∧ q ≫ pullback.snd π b = a ≫ κ := by
  have hc : c ≫ π = (a ≫ κ) ≫ b :=
    h.w.trans ((congrArg (fun k => a ≫ k) hp).trans (Category.assoc _ _ _).symm)
  let q : X ⟶ pullback π b := pullback.lift c (a ≫ κ) hc
  have hqf : q ≫ pullback.fst π b = c := pullback.lift_fst _ _ _
  have hqs : q ≫ pullback.snd π b = a ≫ κ := pullback.lift_snd _ _ _
  have hout : IsPullback (q ≫ pullback.fst π b) a π (κ ≫ b) := by
    rw [hqf, ← hp]
    exact h
  exact ⟨q, hout.of_right hqs (IsPullback.of_hasPullback π b), hqf, hqs⟩

/-- The translated simple curve compares with the specified partial-flag
fibre in a Cartesian square, preserving both fibre projections. -/
theorem simpleCurve_raw_comparison
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (G : ReductiveGroupData K)
    (w : G.weylGroup) (i : G.rootBase.support)
    (F Q : Over (Spec (.of S))) (π : F ⟶ Q)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qQ : (partialFlagVariety G {i}).scheme ⟶ Q.left)
    (hπ : IsPullback (partialFlagMorphism G {i}).left qF qQ π.left)
    (b : Over.mk (𝟙 (Spec (.of S))) ⟶ Q)
    (hb : ((weylFlagPoint G w).val ≫ (partialFlagMorphism G {i}).left) ≫ qQ =
      Spec.map (CommRingCat.ofHom (algebraMap S K)) ≫ b.left) :
    ∃ q : (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).scheme ⟶
        pullback π.left b.left,
      IsPullback q
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
        (pullback.snd π.left b.left)
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
      q ≫ pullback.fst π.left b.left = (simpleSchubertCurve G w i).left ≫ qF ∧
      q ≫ pullback.snd π.left b.left =
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec ≫
          Spec.map (CommRingCat.ofHom (algebraMap S K)) := by
  exact fibre_coefficient_square ((simpleSchubertCurve G w i).left ≫ qF)
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
    π.left _ b.left (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    ((simpleSchubertCurve_isPullback G w i).paste_horiz hπ.flip) hb

private def base_point_map {B : Scheme.{u}} (X : Over B) {Q : Over B}
    (b : Over.mk (𝟙 B) ⟶ Q) : X ⟶ Q :=
  Over.homMk (X.hom ≫ b.left) (by
    rw [Category.assoc, b.w]
    change X.hom ≫ 𝟙 B = X.hom
    exact Category.comp_id _)

private theorem constant_triangle {T : Type*} [Category T]
    {X Y B K Q : T} (q : X ⟶ Y) (a : Y ⟶ B) (n : X ⟶ K)
    (κ : K ⟶ B) (b : B ⟶ Q) (hq : q ≫ a = n ≫ κ) :
    q ≫ (a ≫ b) = n ≫ (κ ≫ b) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ b) hq).trans (Category.assoc _ _ _))

private def curve_stage_result
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {XK FK : Over (Spec (.of K))} {F Q : Over (Spec (.of S))}
    (π : F ⟶ Q) (b : Over.mk (𝟙 (Spec (.of S))) ⟶ Q)
    (fK : XK ⟶ FK) (qF : FK.left ⟶ F.left)
    (q : XK.left ⟶ (fibreModel π b).left)
    (h : IsPullback q XK.hom (fibreModel π b).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (qStd : XK.left ⟶ projectiveScheme S (ULift.{u} (Fin 2)))
    (hStd : IsPullback qStd XK.hom (projectiveToSpec S (ULift.{u} (Fin 2)))
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (qR : ∀ k : CoefficientStage S, XK.left ⟶ projectiveScheme k.val (ULift.{u} (Fin 2)))
    (start : CoefficientStage S) : Prop :=
  let P := Over.mk (projectiveToSpec S (ULift.{u} (Fin 2)))
  let W := fibreModel π b
  let EGeneric := chosenPairIso (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    P W XK.hom qStd q hStd h
  ∃ (k : CoefficientStage S) (_ : start ≤ k)
    (E₀ : stageScalarModel S P.hom k ≅ stageScalarModel S W.hom k)
    (E : Over.mk (projectiveToSpec k.val (ULift.{u} (Fin 2))) ≅ stageScalarModel S W.hom k)
    (qC : XK.left ⟶ (stageScalarModel S W.hom k).left)
    (qF₀ : FK.left ⟶ (stageScalarModel S F.hom k).left),
    E = projectiveStageIso S (ULift.{u} (Fin 2)) k ≪≫ E₀ ∧
    ((modelScalarCone S P.hom).π.app (op k) ≫ E₀.hom.left =
      EGeneric.hom.left ≫ (modelScalarCone S W.hom).π.app (op k)) ∧
    ((modelScalarCone S W.hom).π.app (op k) ≫ E₀.inv.left =
      EGeneric.inv.left ≫ (modelScalarCone S P.hom).π.app (op k)) ∧
    IsPullback qC XK.hom (stageScalarModel S W.hom k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
    IsPullback qF₀ FK.hom (stageScalarModel S F.hom k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
    qC ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) W.hom = q ∧
    qF₀ ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) F.hom = qF ∧
    qC = qR k ≫ E.hom.left ∧
    fK.left ≫ qF₀ = qC ≫ (chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
        (fibreProjection π b)).left ∧
    IsPullback (chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
        (fibreProjection π b)).left (stageScalarModel S W.hom k).hom
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) π).left
      (scalarSection
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
          Q.hom b.left b.w)

private theorem retain_curve_incidence
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {XK FK : Over (Spec (.of K))} {F Q : Over (Spec (.of S))}
    [LocallyOfFiniteType Q.hom] (π : F ⟶ Q)
    [LocallyOfFinitePresentation π.left] [QuasiCompact π.left] [IsSeparated π.left]
    (b : Over.mk (𝟙 (Spec (.of S))) ⟶ Q) (fK : XK ⟶ FK)
    (qF : FK.left ⟶ F.left)
    (hF : IsPullback qF FK.hom F.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (q : XK.left ⟶ (fibreModel π b).left)
    (h : IsPullback q XK.hom (fibreModel π b).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hq : q ≫ (fibreProjection π b).left = fK.left ≫ qF)
    (qStd : XK.left ⟶ projectiveScheme S (ULift.{u} (Fin 2)))
    (hStd : IsPullback qStd XK.hom (projectiveToSpec S (ULift.{u} (Fin 2)))
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (qR : ∀ k : CoefficientStage S, XK.left ⟶ projectiveScheme k.val (ULift.{u} (Fin 2)))
    (hcoeff : ∀ k : CoefficientStage S,
      qR k ≫ (projectiveStageIso S (ULift.{u} (Fin 2)) k).hom.left =
        hStd.flip.isoOverPullback.hom.left ≫
          genericLeg S (projectiveToSpec S (ULift.{u} (Fin 2))) k)
    (start : CoefficientStage S) :
    curve_stage_result S π b fK qF q h qStd hStd qR start := by
  let P : Over (Spec (.of S)) := Over.mk (projectiveToSpec S (ULift.{u} (Fin 2)))
  let W := fibreModel π b
  let : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  let : CompactSpace P.left :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveToSpec S (ULift.{u} (Fin 2)))
  let : LocallyOfFinitePresentation P.hom := inferInstanceAs
    (LocallyOfFinitePresentation (projectiveToSpec S (ULift.{u} (Fin 2))))
  let : IsLocallyNoetherian P.left := LocallyOfFiniteType.isLocallyNoetherian P.hom
  let : QuasiSeparatedSpace P.left := inferInstance
  let : LocallyOfFinitePresentation W.hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback π.left b.left) inferInstance
  let : QuasiCompact W.hom := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback π.left b.left) inferInstance
  let : IsSeparated W.hom := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback π.left b.left) inferInstance
  let : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace W.hom
  let : QuasiSeparatedSpace W.left := quasiSeparatedSpace_of_quasiSeparated W.hom
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let EGeneric := chosenPairIso κ P W XK.hom qStd q hStd h
  have heStd : qStd ≫ (base_point_map P b).left = XK.hom ≫ (κ ≫ b.left) :=
    constant_triangle qStd P.hom XK.hom κ b.left hStd.w
  have heW : q ≫ (base_point_map W b).left = XK.hom ≫ (κ ≫ b.left) :=
    constant_triangle q W.hom XK.hom κ b.left h.w
  have he : EGeneric.hom ≫ chosenScalarArrow κ (base_point_map W b) =
      chosenScalarArrow κ (base_point_map P b) :=
    chosenPairIso_endpoint κ P W Q XK.hom qStd q hStd h
      (base_point_map P b) (base_point_map W b) XK.hom (κ ≫ b.left) heStd heW
  apply bind_witness (exists_chosen_endpoint_iso S hS P W Q
    (base_point_map P b) (base_point_map W b) EGeneric he start)
  intro k hk
  obtain ⟨hstart, E₀, hhom, hinv, _⟩ := hk
  let E : Over.mk (projectiveToSpec k.val (ULift.{u} (Fin 2))) ≅
      stageScalarModel S W.hom k := projectiveStageIso S (ULift.{u} (Fin 2)) k ≪≫ E₀
  let qC := modelStageMap S W.hom XK.hom q h k
  let qF₀ := modelStageMap S F.hom FK.hom qF hF k
  have hcommon : hStd.flip.isoOverPullback.hom.left ≫ EGeneric.hom.left =
      h.flip.isoOverPullback.hom.left :=
    congrArg (fun f => f.left)
      (scalarComparison_iso_triangle hStd.flip.isoOverPullback h.flip.isoOverPullback)
  have hn : qC = qR k ≫ E.hom.left :=
    scalarCurve_comparison_triangle hStd.flip.isoOverPullback.hom.left
      h.flip.isoOverPullback.hom.left
      EGeneric.hom.left (genericLeg S P.hom k) (genericLeg S W.hom k) E₀.hom.left
      (projectiveStageIso S (ULift.{u} (Fin 2)) k).hom.left (qR k) E.hom.left qC
      hcommon hhom (hcoeff k) rfl rfl
  exact ⟨k, hstart, E₀, E, qC, qF₀, rfl, hhom, hinv,
    modelStageMap_cartesian S W.hom XK.hom q h k,
    modelStageMap_cartesian S F.hom FK.hom qF hF k,
    modelStageMap_projection S W.hom XK.hom q h k,
    modelStageMap_projection S F.hom FK.hom qF hF k, hn,
    (modelStageMap_naturality S fK (fibreProjection π b) q qF h hF hq k).symm,
    scalarFibre_cartesian _ π b⟩

end SchubertGeometry
