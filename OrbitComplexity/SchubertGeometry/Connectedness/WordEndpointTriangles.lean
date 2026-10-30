import OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointModels
import OrbitComplexity.SchubertGeometry.Connectedness.ChosenPairedRetention
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Endpoint triangles on a prescribed scalar flag model

A shared comparison to a fixed scalar flag model determines the comparisons
for an entire family of endpoint and inclusion triangles. Both projections
to the original models are retained, and every endpoint remains the specified
scalar extension of its original arrow.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section
universe u v

namespace SchubertGeometry

open private source_scalar_square
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointModels

private theorem prescribed_scalar_square {B BK T X Y : Scheme.{u}}
    (κ : T ⟶ B) (ρ : BK ⟶ T) (σ : BK ⟶ B)
    (a : X ⟶ BK) (b : Y ⟶ B) (q : X ⟶ Y)
    (hρ : ρ ≫ κ = σ) (h : IsPullback q a b σ)
    (qT : X ⟶ pullback κ b)
    (hfst : qT ≫ pullback.fst κ b = a ≫ ρ)
    (hsnd : qT ≫ pullback.snd κ b = q) :
    IsPullback qT a (pullback.fst κ b) ρ := by
  obtain ⟨q₀, hf, hs, hc⟩ := source_scalar_square κ ρ σ a b q hρ h
  have he : q₀ = qT := pullback.hom_ext (hf.trans hfst.symm) (hs.trans hsnd.symm)
  exact he ▸ hc

private theorem scalarArrow_isPullback {B T : Scheme.{u}} (κ : T ⟶ B)
    {C D : Over B} (e : C ⟶ D) :
    IsPullback (chosenScalarArrow κ e).left (pullback.snd κ C.hom)
      (pullback.snd κ D.hom) e.left := by
  have hC : IsPullback (pullback.fst κ C.hom) (pullback.snd κ C.hom) κ C.hom :=
    IsPullback.of_hasPullback κ C.hom
  have hD : IsPullback (pullback.fst κ D.hom) (pullback.snd κ D.hom) κ D.hom :=
    IsPullback.of_hasPullback κ D.hom
  have houter : IsPullback
      ((chosenScalarArrow κ e).left ≫ pullback.fst κ D.hom)
      (pullback.snd κ C.hom) κ (e.left ≫ D.hom) := by
    have hw : (chosenScalarArrow κ e).left ≫ pullback.fst κ D.hom =
        pullback.fst κ C.hom := (chosenScalarArrow κ e).w
    rw [hw, e.w]
    exact hC
  exact houter.of_right (chosenScalarArrow_snd κ e) hD

private theorem scalar_triangle {B BK T : Scheme.{u}} (κ : T ⟶ B) (ρ : BK ⟶ T)
    {C D : Over B} {CK DK : Over BK} (e : C ⟶ D) (eK : CK ⟶ DK)
    (qC : CK.left ⟶ C.left) (qD : DK.left ⟶ D.left)
    (he : qC ≫ e.left = eK.left ≫ qD)
    (qCT : CK.left ⟶ pullback κ C.hom) (qDT : DK.left ⟶ pullback κ D.hom)
    (hCf : qCT ≫ pullback.fst κ C.hom = CK.hom ≫ ρ)
    (hCs : qCT ≫ pullback.snd κ C.hom = qC)
    (hDf : qDT ≫ pullback.fst κ D.hom = DK.hom ≫ ρ)
    (hDs : qDT ≫ pullback.snd κ D.hom = qD) :
    qCT ≫ (chosenScalarArrow κ e).left = eK.left ≫ qDT := by
  apply pullback.hom_ext
  · calc
      (qCT ≫ (chosenScalarArrow κ e).left) ≫ pullback.fst κ D.hom =
          qCT ≫ ((chosenScalarArrow κ e).left ≫ pullback.fst κ D.hom) :=
        Category.assoc _ _ _
      _ = qCT ≫ pullback.fst κ C.hom :=
        congrArg (fun z => qCT ≫ z) (chosenScalarArrow κ e).w
      _ = CK.hom ≫ ρ := hCf
      _ = (eK.left ≫ DK.hom) ≫ ρ :=
        congrArg (fun z => z ≫ ρ) eK.w.symm
      _ = eK.left ≫ (DK.hom ≫ ρ) := Category.assoc _ _ _
      _ = eK.left ≫ (qDT ≫ pullback.fst κ D.hom) :=
        congrArg (fun z => eK.left ≫ z) hDf.symm
      _ = (eK.left ≫ qDT) ≫ pullback.fst κ D.hom :=
        (Category.assoc _ _ _).symm
  · calc
      (qCT ≫ (chosenScalarArrow κ e).left) ≫ pullback.snd κ D.hom =
          qCT ≫ ((chosenScalarArrow κ e).left ≫ pullback.snd κ D.hom) :=
        Category.assoc _ _ _
      _ = qCT ≫ (pullback.snd κ C.hom ≫ e.left) :=
        congrArg (fun z => qCT ≫ z) (chosenScalarArrow_snd κ e)
      _ = (qCT ≫ pullback.snd κ C.hom) ≫ e.left :=
        (Category.assoc _ _ _).symm
      _ = qC ≫ e.left := congrArg (fun z => z ≫ e.left) hCs
      _ = eK.left ≫ qD := he
      _ = eK.left ≫ (qDT ≫ pullback.snd κ D.hom) :=
        congrArg (fun z => eK.left ≫ z) hDs.symm
      _ = (eK.left ≫ qDT) ≫ pullback.snd κ D.hom :=
        (Category.assoc _ _ _).symm

/-- A prescribed scalar flag comparison synchronizes the source and target
comparisons of endpoint triangles. The endpoints and closed inclusions are
the scalar extensions of the given arrows, with both original-model
projections and both triangle equations preserved. -/
theorem scalar_endpoint_triangles {B BK T : Scheme.{u}} {I : Type v}
    (κ : T ⟶ B) (ρ : BK ⟶ T) (σ : BK ⟶ B) (hρ : ρ ≫ κ = σ)
    (A D : I → Over B) (F : Over B)
    (AK DK : I → Over BK) (FK : Over BK)
    (e : ∀ i, A i ⟶ D i) (j : ∀ i, D i ⟶ F)
    [∀ i, IsProper (e i).left] [∀ i, IsClosedImmersion (j i).left]
    (eK : ∀ i, AK i ⟶ DK i) (jK : ∀ i, DK i ⟶ FK)
    (qA : ∀ i, (AK i).left ⟶ (A i).left)
    (qD : ∀ i, (DK i).left ⟶ (D i).left) (qF : FK.left ⟶ F.left)
    (hA : ∀ i, IsPullback (qA i) (AK i).hom (A i).hom σ)
    (hD : ∀ i, IsPullback (qD i) (DK i).hom (D i).hom σ)
    (hF : IsPullback qF FK.hom F.hom σ)
    (he : ∀ i, qA i ≫ (e i).left = (eK i).left ≫ qD i)
    (hj : ∀ i, qD i ≫ (j i).left = (jK i).left ≫ qF)
    (qFT : FK.left ⟶ pullback κ F.hom)
    (hFf : qFT ≫ pullback.fst κ F.hom = FK.hom ≫ ρ)
    (hFs : qFT ≫ pullback.snd κ F.hom = qF) :
    ∃ (qAT : ∀ i, (AK i).left ⟶ pullback κ (A i).hom)
      (qDT : ∀ i, (DK i).left ⟶ pullback κ (D i).hom),
      IsPullback qFT FK.hom (pullback.fst κ F.hom) ρ ∧
      ∀ i, qAT i ≫ pullback.fst κ (A i).hom = (AK i).hom ≫ ρ ∧
        qAT i ≫ pullback.snd κ (A i).hom = qA i ∧
        IsPullback (qAT i) (AK i).hom (pullback.fst κ (A i).hom) ρ ∧
        qDT i ≫ pullback.fst κ (D i).hom = (DK i).hom ≫ ρ ∧
        qDT i ≫ pullback.snd κ (D i).hom = qD i ∧
        IsPullback (qDT i) (DK i).hom (pullback.fst κ (D i).hom) ρ ∧
        qAT i ≫ (chosenScalarArrow κ (e i)).left = (eK i).left ≫ qDT i ∧
        qDT i ≫ (chosenScalarArrow κ (j i)).left = (jK i).left ≫ qFT ∧
        IsProper (chosenScalarArrow κ (e i)).left ∧
        IsClosedImmersion (chosenScalarArrow κ (j i)).left := by
  classical
  choose qAT hAf hAs hAc using fun i =>
    source_scalar_square κ ρ σ (AK i).hom (A i).hom (qA i) hρ (hA i)
  choose qDT hDf hDs hDc using fun i =>
    source_scalar_square κ ρ σ (DK i).hom (D i).hom (qD i) hρ (hD i)
  refine ⟨qAT, qDT, prescribed_scalar_square κ ρ σ FK.hom F.hom qF hρ hF
    qFT hFf hFs, ?_⟩
  intro i
  have heT := scalar_triangle κ ρ (e i) (eK i) (qA i) (qD i) (he i)
    (qAT i) (qDT i) (hAf i) (hAs i) (hDf i) (hDs i)
  have hjT := scalar_triangle κ ρ (j i) (jK i) (qD i) qF (hj i)
    (qDT i) qFT (hDf i) (hDs i) hFf hFs
  have hp : IsProper (chosenScalarArrow κ (e i)).left :=
    MorphismProperty.of_isPullback (P := @IsProper) (scalarArrow_isPullback κ (e i)).flip
      inferInstance
  have hc : IsClosedImmersion (chosenScalarArrow κ (j i)).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (scalarArrow_isPullback κ (j i)).flip
      inferInstance
  exact ⟨hAf i, hAs i, hAc i, hDf i, hDs i, hDc i, heT, hjT, hp, hc⟩

end SchubertGeometry
