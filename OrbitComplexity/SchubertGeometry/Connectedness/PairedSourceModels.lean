import OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointArrows
import OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected
import OrbitComplexity.SchubertGeometry.Connectedness.EmptyEndpointStage
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Prescribed paired sources and a Cartesian flag model

Scalar extensions of the prescribed source and target retain their
endpoint and closed inclusion in any Cartesian model of the same flag.
The source and target projections are kept with both comparison squares.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting

noncomputable section
universe u

namespace SchubertGeometry

open private cartesian_over_iso
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointArrows
open private stage_map stage_map_cartesian stage_map_original scalar_property
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected
open private scalar_comparison
  from OrbitComplexity.SchubertGeometry.Connectedness.EmptyEndpointStage

private theorem flag_comparison_iso {B T BK : Scheme.{u}}
    (κ : T ⟶ B) (ρ : BK ⟶ T) (P : Over B) (F : Over T) (FK : Over BK)
    (π : F.left ⟶ P.left) (hπ : IsPullback π F.hom P.hom κ)
    (qP : FK.left ⟶ P.left) (qF : FK.left ⟶ F.left)
    (qStd : FK.left ⟶ pullback κ P.hom)
    (hF : IsPullback qF FK.hom F.hom ρ)
    (hStd : IsPullback qStd FK.hom (pullback.fst κ P.hom) ρ)
    (hOld : qF ≫ π = qP) (hStdOld : qStd ≫ pullback.snd κ P.hom = qP) :
    ∃ E : F ≅ Over.mk (pullback.fst κ P.hom),
      E.hom.left ≫ pullback.snd κ P.hom = π ∧ qF ≫ E.hom.left = qStd := by
  obtain ⟨E, hE⟩ := cartesian_over_iso κ F P π hπ
  refine ⟨E, hE, ?_⟩
  apply pullback.hom_ext
  · calc
      (qF ≫ E.hom.left) ≫ pullback.fst κ P.hom = qF ≫ F.hom := by
        change (qF ≫ E.hom.left) ≫ (Over.mk (pullback.fst κ P.hom)).hom =
          qF ≫ F.hom
        rw [Category.assoc, E.hom.w]
      _ = FK.hom ≫ ρ := hF.w
      _ = qStd ≫ pullback.fst κ P.hom := hStd.w.symm
  · calc
      (qF ≫ E.hom.left) ≫ pullback.snd κ P.hom = qF ≫ π := by
        rw [Category.assoc, hE]
      _ = qP := hOld
      _ = qStd ≫ pullback.snd κ P.hom := hStdOld.symm

private theorem square_to_iso_target {C : Type*} [Category C]
    {A B X Y Z : C} (E : X ≅ Y) (q : A ⟶ B) (r : B ⟶ Y)
    (rK : A ⟶ Z) (qF : Z ⟶ X) (qStd : Z ⟶ Y)
    (h : q ≫ r = rK ≫ qStd) (hF : qF ≫ E.hom = qStd) :
    q ≫ (r ≫ E.inv) = rK ≫ qF := by
  apply (cancel_mono E.hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hF] using h

private theorem paired_source_models
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (C D P : Over (Spec (.of S))) (e : C ⟶ D) (r : D ⟶ P)
    [IsClosedImmersion r.left]
    (CK DK FK : Over (Spec (.of K))) (eK : CK ⟶ DK) (rK : DK ⟶ FK)
    (qC : CK.left ⟶ C.left) (qD : DK.left ⟶ D.left) (qP : FK.left ⟶ P.left)
    (hC : IsPullback qC CK.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD DK.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hP : IsPullback qP FK.hom P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (he : qC ≫ e.left = eK.left ≫ qD) (hr : qD ≫ r.left = rK.left ≫ qP)
    (k : CoefficientStage S) (F : Over (Spec (.of k.val)))
    (π : F.left ⟶ P.left)
    (hπ : IsPullback π F.hom P.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)))
    (qF : FK.left ⟶ F.left)
    (hF : IsPullback qF FK.hom F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))))
    (hOld : qF ≫ π = qP) :
    let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
    ∃ (rT : stageScalarModel S D.hom k ⟶ F)
      (qCT : CK.left ⟶ (stageScalarModel S C.hom k).left)
      (qDT : DK.left ⟶ (stageScalarModel S D.hom k).left),
      IsClosedImmersion rT.left ∧
      IsPullback qCT CK.hom (stageScalarModel S C.hom k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
      IsPullback qDT DK.hom (stageScalarModel S D.hom k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
      qCT ≫ pullback.snd κ C.hom = qC ∧
      qDT ≫ pullback.snd κ D.hom = qD ∧
      qCT ≫ (chosenScalarArrow κ e).left = eK.left ≫ qDT ∧
      qDT ≫ rT.left = rK.left ≫ qF := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k.val K))
  let qCT := stage_map S C CK qC hC k
  let qDT := stage_map S D DK qD hD k
  let qStd := stage_map S P FK qP hP k
  have hCT := stage_map_cartesian S C CK qC hC k
  have hDT := stage_map_cartesian S D DK qD hD k
  have hStd := stage_map_cartesian S P FK qP hP k
  have hCTo := stage_map_original S C CK qC hC k
  have hDTo := stage_map_original S D DK qD hD k
  have hStdOld := stage_map_original S P FK qP hP k
  obtain ⟨E, _hE, hEq⟩ := flag_comparison_iso κ ρ P F FK π hπ
    qP qF qStd hF hStd hOld hStdOld
  let rT : stageScalarModel S D.hom k ⟶ F := chosenScalarArrow κ r ≫ E.inv
  have hclosed₀ := scalar_property (@IsClosedImmersion) κ r inferInstance
  let : IsClosedImmersion (chosenScalarArrow κ r).left := hclosed₀
  have hclosed : IsClosedImmersion rT.left := by
    change IsClosedImmersion ((chosenScalarArrow κ r).left ≫ E.inv.left)
    infer_instance
  have heT := scalar_comparison κ ρ e eK qC qD qCT qDT hCT hDT hCTo hDTo he
  have hrStd := scalar_comparison κ ρ r rK qD qP qDT qStd hDT hStd hDTo hStdOld hr
  have hrT : qDT ≫ rT.left = rK.left ≫ qF :=
    square_to_iso_target ((Over.forget _).mapIso E) qDT
      (chosenScalarArrow κ r).left rK.left qF qStd hrStd hEq
  exact ⟨rT, qCT, qDT, hclosed, hCT, hDT, hCTo, hDTo, heT, hrT⟩

end SchubertGeometry
