import OrbitComplexity.SchubertGeometry.Connectedness.ChosenPairedRetention
import OrbitComplexity.GroupActions.Varieties.Basic
import Batteries.Tactic.Lint

/-! # Cartesian comparisons of scalar diagrams -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace SchubertGeometry
universe u

/-- A morphism to a variety commutes with its structure map to the coefficient
spectrum. -/
theorem map_to_variety_base {K : Type u} [Field K]
    (C : Over (Spec (.of K))) (V : GroupActions.Variety K) (f : C ⟶ V.toOver) :
    f.left ≫ V.toSpec = C.hom := f.w

/-- A morphism of varieties commutes with their structure maps to the coefficient
spectrum. -/
theorem varietyMap_base {K : Type u} [Field K]
    (V W : GroupActions.Variety K) (f : V.toOver ⟶ W.toOver) :
    f.left ≫ W.toSpec = V.toSpec := f.w

/-- A scalar extension of a three-object diagram retains its Cartesian
comparisons, original projections, and the two arrow squares. -/
def diagramStageData {B T BK X Y Z : Scheme.{u}}
    (κ : T ⟶ B) (ρ : BK ⟶ T) (C D F : Over B)
    (x : X ⟶ BK) (y : Y ⟶ BK) (z : Z ⟶ BK)
    (nE : X ⟶ Y) (nJ : Y ⟶ Z)
    (e : C ⟶ D) (j : D ⟶ F)
    (qC : X ⟶ C.left) (qD : Y ⟶ D.left) (qF : Z ⟶ F.left) : Prop :=
  ∃ (mC : X ⟶ pullback κ C.hom) (mD : Y ⟶ pullback κ D.hom)
    (mF : Z ⟶ pullback κ F.hom),
    IsPullback mC x (pullback.fst κ C.hom) ρ ∧
    IsPullback mD y (pullback.fst κ D.hom) ρ ∧
    IsPullback mF z (pullback.fst κ F.hom) ρ ∧
    mC ≫ pullback.snd κ C.hom = qC ∧
    mD ≫ pullback.snd κ D.hom = qD ∧
    mF ≫ pullback.snd κ F.hom = qF ∧
    mC ≫ (chosenScalarArrow κ e).left = nE ≫ mD ∧
    mD ≫ (chosenScalarArrow κ j).left = nJ ≫ mF

/-- Cartesian comparisons of a three-object diagram factor through a prescribed
coefficient extension, retaining the projections and both arrow squares. -/
theorem diagram_stage_comparisons {B T BK X Y Z : Scheme.{u}}
    (κ : T ⟶ B) (ρ : BK ⟶ T) (σ : BK ⟶ B) (hρ : ρ ≫ κ = σ)
    (C D F : Over B)
    (x : X ⟶ BK) (y : Y ⟶ BK) (z : Z ⟶ BK)
    (nE : X ⟶ Y) (nJ : Y ⟶ Z)
    (hEbase : nE ≫ y = x) (hJbase : nJ ≫ z = y)
    (e : C ⟶ D) (j : D ⟶ F)
    (qC : X ⟶ C.left) (qD : Y ⟶ D.left) (qF : Z ⟶ F.left)
    (hC : IsPullback qC x C.hom σ) (hD : IsPullback qD y D.hom σ)
    (hF : IsPullback qF z F.hom σ)
    (he : qC ≫ e.left = nE ≫ qD) (hj : qD ≫ j.left = nJ ≫ qF) :
    diagramStageData κ ρ C D F x y z nE nJ e j qC qD qF := by
  have hwC : (x ≫ ρ) ≫ κ = qC ≫ C.hom := by
    rw [Category.assoc, hρ]
    exact hC.w.symm
  have hwD : (y ≫ ρ) ≫ κ = qD ≫ D.hom := by
    rw [Category.assoc, hρ]
    exact hD.w.symm
  have hwF : (z ≫ ρ) ≫ κ = qF ≫ F.hom := by
    rw [Category.assoc, hρ]
    exact hF.w.symm
  let mC : X ⟶ pullback κ C.hom := pullback.lift (x ≫ ρ) qC hwC
  let mD : Y ⟶ pullback κ D.hom := pullback.lift (y ≫ ρ) qD hwD
  let mF : Z ⟶ pullback κ F.hom := pullback.lift (z ≫ ρ) qF hwF
  have hfC : mC ≫ pullback.fst κ C.hom = x ≫ ρ := pullback.lift_fst _ _ _
  have hfD : mD ≫ pullback.fst κ D.hom = y ≫ ρ := pullback.lift_fst _ _ _
  have hfF : mF ≫ pullback.fst κ F.hom = z ≫ ρ := pullback.lift_fst _ _ _
  have hpC : mC ≫ pullback.snd κ C.hom = qC := pullback.lift_snd _ _ _
  have hpD : mD ≫ pullback.snd κ D.hom = qD := pullback.lift_snd _ _ _
  have hpF : mF ≫ pullback.snd κ F.hom = qF := pullback.lift_snd _ _ _
  have hCt : IsPullback mC x (pullback.fst κ C.hom) ρ := by
    have ho : IsPullback (mC ≫ pullback.snd κ C.hom) x C.hom (ρ ≫ κ) := by
      rw [hpC, hρ]
      exact hC
    exact ho.of_right hfC (IsPullback.of_hasPullback κ C.hom).flip
  have hDt : IsPullback mD y (pullback.fst κ D.hom) ρ := by
    have ho : IsPullback (mD ≫ pullback.snd κ D.hom) y D.hom (ρ ≫ κ) := by
      rw [hpD, hρ]
      exact hD
    exact ho.of_right hfD (IsPullback.of_hasPullback κ D.hom).flip
  have hFt : IsPullback mF z (pullback.fst κ F.hom) ρ := by
    have ho : IsPullback (mF ≫ pullback.snd κ F.hom) z F.hom (ρ ≫ κ) := by
      rw [hpF, hρ]
      exact hF
    exact ho.of_right hfF (IsPullback.of_hasPullback κ F.hom).flip
  have het : mC ≫ (chosenScalarArrow κ e).left = nE ≫ mD := by
    apply pullback.hom_ext
    · calc
        _ = mC ≫ pullback.fst κ C.hom :=
          (Category.assoc _ _ _).trans
            (congrArg (fun a => mC ≫ a) (chosenScalarArrow κ e).w)
        _ = x ≫ ρ := hfC
        _ = (nE ≫ mD) ≫ pullback.fst κ D.hom := by
          rw [Category.assoc, hfD, ← Category.assoc, hEbase]
    · calc
        _ = (mC ≫ pullback.snd κ C.hom) ≫ e.left := by
          rw [Category.assoc, chosenScalarArrow_snd, ← Category.assoc]
        _ = qC ≫ e.left := congrArg (fun a => a ≫ e.left) hpC
        _ = nE ≫ qD := he
        _ = (nE ≫ mD) ≫ pullback.snd κ D.hom := by rw [Category.assoc, hpD]
  have hjt : mD ≫ (chosenScalarArrow κ j).left = nJ ≫ mF := by
    apply pullback.hom_ext
    · calc
        _ = mD ≫ pullback.fst κ D.hom :=
          (Category.assoc _ _ _).trans
            (congrArg (fun a => mD ≫ a) (chosenScalarArrow κ j).w)
        _ = y ≫ ρ := hfD
        _ = (nJ ≫ mF) ≫ pullback.fst κ F.hom := by
          rw [Category.assoc, hfF, ← Category.assoc, hJbase]
    · calc
        _ = (mD ≫ pullback.snd κ D.hom) ≫ j.left := by
          rw [Category.assoc, chosenScalarArrow_snd, ← Category.assoc]
        _ = qD ≫ j.left := congrArg (fun a => a ≫ j.left) hpD
        _ = nJ ≫ qF := hj
        _ = (nJ ≫ mF) ≫ pullback.snd κ F.hom := by rw [Category.assoc, hpF]
  exact ⟨mC, mD, mF, hCt, hDt, hFt, hpC, hpD, hpF, het, hjt⟩

end SchubertGeometry
