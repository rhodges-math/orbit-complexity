import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.BSDH.Surjectivity
import OrbitComplexity.SchubertGeometry.Connectedness.ChosenPairedRetention
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.StageEquations
import Mathlib.AlgebraicGeometry.Noetherian

set_option autoImplicit false

/-! # The empty-word endpoint over its chosen coefficient models

The point endpoint is an isomorphism. Its inverse and its equation with
the specified model morphism are retained at a common coefficient stage.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open FrobeniusSplitting Opposite

namespace SchubertGeometry

universe u

private theorem iso_gc {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    GeometricallyConnected f := by
  constructor
  intro L _ y Z a b h
  let : IsIso b := h.isIso_snd_of_isIso
  exact b.homeomorph.connectedSpace_iff.mpr inferInstance

private theorem field_connected {X Y : Scheme.{u}} (f : X ⟶ Y)
    [GeometricallyConnected f] (L : Type u) [Field L] (y : Spec (.of L) ⟶ Y) :
    ConnectedSpace (pullback f y : Scheme.{u}) := by
  let : GeometricallyConnected (pullback.snd f y) := inferInstance
  exact GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd f y)

private theorem iso_from_arrow_eq {B : Scheme.{u}} {X Y : Over B}
    (E : X ≅ Y) (f : X ⟶ Y) (h : f = E.hom) : IsIso f.left := by
  subst f
  infer_instance

private theorem scalar_comparison {B BK T : Scheme.{u}} (κ : T ⟶ B) (ρ : BK ⟶ T)
    {X Y : Over B} {U V : Over BK} (f : X ⟶ Y) (g : U ⟶ V)
    (qX : U.left ⟶ X.left) (qY : V.left ⟶ Y.left)
    (qXT : U.left ⟶ (Over.mk (pullback.fst κ X.hom)).left)
    (qYT : V.left ⟶ (Over.mk (pullback.fst κ Y.hom)).left)
    (hXT : IsPullback qXT U.hom (pullback.fst κ X.hom) ρ)
    (hYT : IsPullback qYT V.hom (pullback.fst κ Y.hom) ρ)
    (hXo : qXT ≫ pullback.snd κ X.hom = qX)
    (hYo : qYT ≫ pullback.snd κ Y.hom = qY)
    (h : qX ≫ f.left = g.left ≫ qY) :
    qXT ≫ (chosenScalarArrow κ f).left = g.left ≫ qYT := by
  apply pullback.hom_ext
  · calc
      (qXT ≫ (chosenScalarArrow κ f).left) ≫ pullback.fst κ Y.hom =
          qXT ≫ pullback.fst κ X.hom :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t => qXT ≫ t) (chosenScalarArrow κ f).w)
      _ = U.hom ≫ ρ := hXT.w
      _ = (g.left ≫ qYT) ≫ pullback.fst κ Y.hom := by
        rw [Category.assoc, hYT.w, ← Category.assoc, g.w]
  · calc
      (qXT ≫ (chosenScalarArrow κ f).left) ≫ pullback.snd κ Y.hom =
          qXT ≫ (pullback.snd κ X.hom ≫ f.left) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t => qXT ≫ t) (chosenScalarArrow_snd κ f))
      _ = qX ≫ f.left := (Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ f.left) hXo)
      _ = g.left ≫ qY := h
      _ = (g.left ≫ qYT) ≫ pullback.snd κ Y.hom :=
        (congrArg (fun t => g.left ≫ t) hYo.symm).trans (Category.assoc _ _ _).symm

private theorem cone_original {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (X : Over (Spec (.of S))) (i : CoefficientStage S) :
    (modelScalarCone S X.hom).π.app (op i) ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) X.hom =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) X.hom := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  exact pullback.lift_snd _ _ _

private theorem original_triangle {T : Type*} [Category T] {A B C D : T}
    (e : A ⟶ B) (q : B ⟶ C) (s : C ⟶ D) (p : B ⟶ D) (f : A ⟶ D)
    (hq : q ≫ s = p) (he : e ≫ p = f) : (e ≫ q) ≫ s = f :=
  (Category.assoc _ _ _).trans ((congrArg (fun t => e ≫ t) hq).trans he)

private theorem cancel_triangle {T : Type*} [Category T]
    {U V X Y A B : T} (E : U ≅ X) (F : V ≅ Y)
    (g : U ⟶ V) (p : X ⟶ A) (q : Y ⟶ B) (f : A ⟶ B)
    (h : (E.hom ≫ p) ≫ f = g ≫ (F.hom ≫ q)) :
    p ≫ f = (E.inv ≫ g ≫ F.hom) ≫ q := by
  calc
    p ≫ f = E.inv ≫ ((E.hom ≫ p) ≫ f) := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = E.inv ≫ (g ≫ (F.hom ≫ q)) := congrArg (fun t => E.inv ≫ t) h
    _ = (E.inv ≫ g ≫ F.hom) ≫ q := by simp only [Category.assoc]

private theorem square_projection {C : Type*} [Category C]
    {A B X Y P Q : C} (e : A ⟶ B) (u : B ⟶ Y) (v : A ⟶ X)
    (m : X ⟶ Y) (x : X ⟶ P) (y : Y ⟶ Q) (f : P ⟶ Q)
    (p : A ⟶ P) (q : B ⟶ Q)
    (h : e ≫ u = v ≫ m) (hm : m ≫ y = x ≫ f)
    (hx : v ≫ x = p) (hy : u ≫ y = q) : e ≫ q = p ≫ f := by
  calc
    e ≫ q = e ≫ (u ≫ y) := congrArg (fun t => e ≫ t) hy.symm
    _ = (e ≫ u) ≫ y := (Category.assoc e u y).symm
    _ = (v ≫ m) ≫ y := congrArg (fun t => t ≫ y) h
    _ = v ≫ (m ≫ y) := Category.assoc v m y
    _ = v ≫ (x ≫ f) := congrArg (fun t => v ≫ t) hm
    _ = (v ≫ x) ≫ f := (Category.assoc v x f).symm
    _ = p ≫ f := congrArg (fun t => t ≫ f) hx

private theorem extend_scalar_arrow {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X Y : Over (Spec (.of S))} (f : X ⟶ Y)
    {i j : CoefficientStage S} (hij : i ≤ j) :
    extendModelMorphism S X.hom Y.hom hij
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) f) =
      chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) f := by
  let κi := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let κj := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  let fi := chosenScalarArrow κi f
  let fj := chosenScalarArrow κj f
  let e := extendModelMorphism S X.hom Y.hom hij fi
  apply (Over.forget (Spec (.of j.val))).map_injective
  change e.left = fj.left
  apply pullback.hom_ext
  · exact e.w.trans fj.w.symm
  · exact (square_projection e.left (stageScalarTransition S Y.hom hij)
      (stageScalarTransition S X.hom hij) fi.left
      (pullback.snd κi X.hom) (pullback.snd κi Y.hom) f.left
      (pullback.snd κj X.hom) (pullback.snd κj Y.hom)
      (extendModelMorphism_transition S X.hom Y.hom hij fi)
      (chosenScalarArrow_snd κi f) (stageScalarTransition_snd S X.hom hij)
      (stageScalarTransition_snd S Y.hom hij)).trans (chosenScalarArrow_snd κj f).symm

private def empty_result {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X Y : Over (Spec (.of S))} (f : X ⟶ Y) (start : CoefficientStage S) : Prop :=
  ∃ (k : CoefficientStage S) (_ : start ≤ k),
    let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
    let fk := chosenScalarArrow κ f
    IsIso fk.left ∧ GeometricallyConnected fk.left ∧
    (fk.left ≫ (stageScalarModel S Y.hom k).hom = (stageScalarModel S X.hom k).hom) ∧
    (fk.left ≫ pullback.snd κ Y.hom = pullback.snd κ X.hom ≫ f.left) ∧
    ∀ (L : Type u) [Field L] (y : Spec (.of L) ⟶ (stageScalarModel S Y.hom k).left),
      ConnectedSpace (pullback fk.left y : Scheme.{u})

private theorem retain_iso_arrow {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG)
    {X Y : Over (Spec (.of S))} [LocallyOfFinitePresentation X.hom]
    [LocallyOfFinitePresentation Y.hom] [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
    {U V : Over (Spec (.of K))} (g : U ⟶ V) [IsIso g.left]
    (qX : U.left ⟶ X.left) (qY : V.left ⟶ Y.left)
    (hX : IsPullback qX U.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY V.hom Y.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (f : X ⟶ Y) (hf : qX ≫ f.left = g.left ≫ qY)
    (start : CoefficientStage S) : empty_result S f start := by
  let EX : U ≅ genericScalarModel S X.hom := hX.flip.isoOverPullback
  let EY : V ≅ genericScalarModel S Y.hom := hY.flip.isoOverPullback
  let EG : U ≅ V := Over.isoMk (asIso g.left) g.w
  let E : genericScalarModel S X.hom ≅ genericScalarModel S Y.hom := EX.symm ≪≫ EG ≪≫ EY
  obtain ⟨i, Ei, hEi, _⟩ := exists_model_iso S hS X.hom Y.hom E
  obtain ⟨j, hij, hstart⟩ := exists_ge_ge i start
  let Ej := retainedIsoExtend S X.hom Y.hom hij Ei
  have hEj : (modelScalarCone S X.hom).π.app (op j) ≫ Ej.hom.left =
      E.hom.left ≫ (modelScalarCone S Y.hom).π.app (op j) :=
    extendModelMorphism_baseChange S X.hom Y.hom hij Ei.hom E.hom hEi
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap j.val K))
  let fj := chosenScalarArrow κ f
  let qXj := EX.hom.left ≫ (modelScalarCone S X.hom).π.app (op j)
  let qYj := EY.hom.left ≫ (modelScalarCone S Y.hom).π.app (op j)
  have hXj := overIso_modelStage_cartesian S X.hom j U EX
  have hYj := overIso_modelStage_cartesian S Y.hom j V EY
  have hXo : qXj ≫ pullback.snd κ X.hom = qX :=
    original_triangle EX.hom.left _ _ _ qX (cone_original S X j)
      hX.flip.isoOverPullback_hom_left_comp_snd
  have hYo : qYj ≫ pullback.snd κ Y.hom = qY :=
    original_triangle EY.hom.left _ _ _ qY (cone_original S Y j)
      hY.flip.isoOverPullback_hom_left_comp_snd
  have hfj : (modelScalarCone S X.hom).π.app (op j) ≫ fj.left =
      E.hom.left ≫ (modelScalarCone S Y.hom).π.app (op j) :=
    cancel_triangle ((Over.forget _).mapIso EX) ((Over.forget _).mapIso EY) g.left _ _ _
      (scalar_comparison κ ρ f g qX qY qXj qYj hXj hYj hXo hYo hf)
  obtain ⟨k, hjk, hmaps⟩ := exists_stage_arrow_eq S hS X.hom Y.hom j fj Ej.hom
    (hfj.trans hEj.symm)
  let Ek := retainedIsoExtend S X.hom Y.hom hjk Ej
  let μ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let fk := chosenScalarArrow μ f
  have heq : fk = Ek.hom := (extend_scalar_arrow S f hjk).symm.trans hmaps
  let : IsIso fk.left := iso_from_arrow_eq Ek fk heq
  let : GeometricallyConnected fk.left := iso_gc fk.left
  exact ⟨k, hstart.trans hjk, inferInstance, inferInstance, fk.w,
    chosenScalarArrow_snd μ f, fun L _ y => field_connected fk.left L y⟩

private theorem empty_endpoint_iso
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced []) :
    IsIso (bsdhSchubertMap G [] hred).left := by
  let f : Spec (.of K) ⟶ (schubertVariety G 1).scheme := (bsdhSchubertMap G [] hred).left
  have hf : f ≫ (schubertVariety G 1).toSpec = 𝟙 _ := by
    have h : f ≫ (schubertVariety G 1).toSpec =
        (baseFlagPoint G).val ≫ (flagVariety G).toSpec := (bsdhSchubertMap G [] hred).w
    exact h.trans (baseFlagPoint G).property
  let : IsClosedImmersion f :=
    isClosedImmersion_of_comp_eq_id (schubertVariety G 1).toSpec f hf
  let : Surjective f := bsdhSchubertMap_surjective G [] hred
  exact isIso_of_isClosedImmersion_of_surjective f

/-- The empty-word endpoint becomes an isomorphism on a coefficient extension
of its specified models, retaining both projections and every field fibre. -/
theorem exists_empty_endpoint_connected
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced [])
    {X Y : Over (Spec (.of S))}
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom]
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom]
    (qX : bsdhScheme G [] ⟶ X.left)
    (qY : (schubertVariety G 1).scheme ⟶ Y.left)
    (hX : IsPullback qX (bsdhToSpec G []) X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY (schubertVariety G 1).toSpec Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (f : X ⟶ Y) (hf : qX ≫ f.left = (bsdhSchubertMap G [] hred).left ≫ qY)
    (start : CoefficientStage S) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k),
      let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
      let fk := chosenScalarArrow κ f
      IsIso fk.left ∧ GeometricallyConnected fk.left ∧
      (fk.left ≫ (stageScalarModel S Y.hom k).hom = (stageScalarModel S X.hom k).hom) ∧
      (fk.left ≫ pullback.snd κ Y.hom = pullback.snd κ X.hom ≫ f.left) ∧
      ∀ (L : Type u) [Field L] (y : Spec (.of L) ⟶ (stageScalarModel S Y.hom k).left),
        ConnectedSpace (pullback fk.left y : Scheme.{u}) := by
  let : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let : IsIso (bsdhSchubertMap G [] hred).left := empty_endpoint_iso G hred
  exact retain_iso_arrow S hS (bsdhSchubertMap G [] hred) qX qY hX hY f hf start

end SchubertGeometry
