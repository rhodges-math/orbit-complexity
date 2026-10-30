import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Batteries.Tactic.Lint

/-! # Image factors after changing the coefficient base

A morphism of coefficient models determines a morphism of their Cartesian
field fibres. A retained endpoint triangle identifies its composite in the
same ambient fibre.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits

namespace SchubertGeometry

private theorem exists_stage_comparison {C : Type u} [Category.{v} C]
    {P A X B T Q : C} (p : P ⟶ A) (t : P ⟶ T) (a : A ⟶ B)
    (σ : T ⟶ B) (ρ : Q ⟶ T) (κ : Q ⟶ B) (hκ : ρ ≫ σ = κ)
    (q : X ⟶ A) (x : X ⟶ Q)
    (hT : IsPullback p t a σ) (hX : IsPullback q x a κ) :
    ∃ qT : X ⟶ P, IsPullback qT x t ρ ∧ qT ≫ p = q ∧ qT ≫ t = x ≫ ρ := by
  have hsquare : q ≫ a = (x ≫ ρ) ≫ σ :=
    hX.w.trans ((congrArg (fun k => x ≫ k) hκ.symm).trans (Category.assoc _ _ _).symm)
  let qT := hT.lift q (x ≫ ρ) hsquare
  have hp : qT ≫ p = q := hT.lift_fst _ _ _
  have ht : qT ≫ t = x ≫ ρ := hT.lift_snd _ _ _
  have houter : IsPullback (qT ≫ p) x a (ρ ≫ σ) := by
    rw [hp, hκ]
    exact hX
  exact ⟨qT, houter.of_right ht hT, hp, ht⟩

private theorem factor_model_triangle {C : Type u} [Category.{v} C]
    {A Y W Z M F C₀ D₀ CT DT : C}
    (g : A ⟶ Y) (a : A ⟶ W) (jY : Y ⟶ Z) (f : W ⟶ Z)
    (qW : W ⟶ M) (qZ : Z ⟶ F) (qA : A ⟶ C₀) (qY : Y ⟶ D₀)
    (c : C₀ ⟶ M) (i : M ⟶ F) (j : D₀ ⟶ F)
    (qAT : A ⟶ CT) (qYT : Y ⟶ DT) (pC : CT ⟶ C₀) (pD : DT ⟶ D₀)
    (e : CT ⟶ DT)
    (hg : g ≫ qYT = qAT ≫ e)
    (hAT : qAT ≫ pC = qA) (hYT : qYT ≫ pD = qY)
    (ha : a ≫ qW = qA ≫ c) (hj : jY ≫ qZ = qY ≫ j)
    (hf : f ≫ qZ = qW ≫ i) (he : e ≫ pD ≫ j = pC ≫ c ≫ i) :
    (g ≫ jY) ≫ qZ = (a ≫ f) ≫ qZ := by
  calc
    (g ≫ jY) ≫ qZ = g ≫ (jY ≫ qZ) := Category.assoc _ _ _
    _ = g ≫ (qY ≫ j) := congrArg (fun k => g ≫ k) hj
    _ = g ≫ ((qYT ≫ pD) ≫ j) := congrArg (fun k => g ≫ (k ≫ j)) hYT.symm
    _ = (g ≫ qYT) ≫ pD ≫ j := by simp only [Category.assoc]
    _ = (qAT ≫ e) ≫ pD ≫ j := congrArg (fun k => k ≫ pD ≫ j) hg
    _ = qAT ≫ (e ≫ pD ≫ j) := by simp only [Category.assoc]
    _ = qAT ≫ (pC ≫ c ≫ i) := congrArg (fun k => qAT ≫ k) he
    _ = (qAT ≫ pC) ≫ c ≫ i := by simp only [Category.assoc]
    _ = qA ≫ c ≫ i := congrArg (fun k => k ≫ c ≫ i) hAT
    _ = (qA ≫ c) ≫ i := (Category.assoc _ _ _).symm
    _ = (a ≫ qW) ≫ i := congrArg (fun k => k ≫ i) ha.symm
    _ = a ≫ (qW ≫ i) := Category.assoc _ _ _
    _ = a ≫ (f ≫ qZ) := congrArg (fun k => a ≫ k) hf.symm
    _ = (a ≫ f) ≫ qZ := (Category.assoc _ _ _).symm

private theorem factor_base_triangle {C : Type u} [Category.{v} C]
    {A Y W Z Q : C} (g : A ⟶ Y) (a : A ⟶ W) (j : Y ⟶ Z) (f : W ⟶ Z)
    (a₀ : A ⟶ Q) (y₀ : Y ⟶ Q) (w₀ : W ⟶ Q) (z₀ : Z ⟶ Q)
    (hg : g ≫ y₀ = a₀) (ha : a ≫ w₀ = a₀)
    (hj : j ≫ z₀ = y₀) (hf : f ≫ z₀ = w₀) :
    (g ≫ j) ≫ z₀ = (a ≫ f) ≫ z₀ := by
  calc
    (g ≫ j) ≫ z₀ = g ≫ (j ≫ z₀) := Category.assoc _ _ _
    _ = g ≫ y₀ := congrArg (fun k => g ≫ k) hj
    _ = a₀ := hg
    _ = a ≫ w₀ := ha.symm
    _ = a ≫ (f ≫ z₀) := congrArg (fun k => a ≫ k) hf.symm
    _ = (a ≫ f) ≫ z₀ := (Category.assoc _ _ _).symm

/-- A coefficient-stage image factor gives a factor on the prescribed
Cartesian fibres, with the same ambient endpoint. The resulting comparisons
to the stage remain Cartesian and retain their original projections. -/
theorem exists_scalar_image_factor {C : Type u} [Category.{v} C]
    {A Y W Z M F C₀ D₀ CT DT B T Q : C}
    (c : C₀ ⟶ M) (i : M ⟶ F) (j : D₀ ⟶ F)
    (c₀ : C₀ ⟶ B) (d₀ : D₀ ⟶ B) (f₀ : F ⟶ B)
    (σ : T ⟶ B) (ρ : Q ⟶ T) (κ : Q ⟶ B) (hκ : ρ ≫ σ = κ)
    (pC : CT ⟶ C₀) (pD : DT ⟶ D₀) (ct : CT ⟶ T) (dt : DT ⟶ T)
    (hCT : IsPullback pC ct c₀ σ) (hDT : IsPullback pD dt d₀ σ)
    (e : CT ⟶ DT) (hebase : e ≫ dt = ct) (he : e ≫ pD ≫ j = pC ≫ c ≫ i)
    (qW : W ⟶ M) (qZ : Z ⟶ F) (w₀ : W ⟶ Q) (z₀ : Z ⟶ Q)
    (hZ : IsPullback qZ z₀ f₀ κ)
    (f : W ⟶ Z) (hfbase : f ≫ z₀ = w₀) (hf : f ≫ qZ = qW ≫ i)
    (a : A ⟶ W) (jY : Y ⟶ Z) (qA : A ⟶ C₀) (qY : Y ⟶ D₀)
    (a₀ : A ⟶ Q) (y₀ : Y ⟶ Q)
    (hA : IsPullback qA a₀ c₀ κ) (hY : IsPullback qY y₀ d₀ κ)
    (habase : a ≫ w₀ = a₀) (hjbase : jY ≫ z₀ = y₀)
    (ha : a ≫ qW = qA ≫ c) (hj : jY ≫ qZ = qY ≫ j) :
    ∃ (qAT : A ⟶ CT) (qYT : Y ⟶ DT) (g : A ⟶ Y),
      IsPullback qAT a₀ ct ρ ∧ IsPullback qYT y₀ dt ρ ∧
      qAT ≫ pC = qA ∧ qYT ≫ pD = qY ∧
      qAT ≫ e = g ≫ qYT ∧ g ≫ y₀ = a₀ ∧ g ≫ jY = a ≫ f := by
  obtain ⟨qAT, hAT, hpC, hct⟩ := exists_stage_comparison pC ct c₀ σ ρ κ hκ qA a₀ hCT hA
  obtain ⟨qYT, hYT, hpD, _⟩ := exists_stage_comparison pD dt d₀ σ ρ κ hκ qY y₀ hDT hY
  have hfactor : (qAT ≫ e) ≫ dt = a₀ ≫ ρ :=
    (Category.assoc _ _ _).trans ((congrArg (fun k => qAT ≫ k) hebase).trans hct)
  let g := hYT.lift (qAT ≫ e) a₀ hfactor
  have hg : g ≫ qYT = qAT ≫ e := hYT.lift_fst _ _ _
  have hgbase : g ≫ y₀ = a₀ := hYT.lift_snd _ _ _
  refine ⟨qAT, qYT, g, hAT, hYT, hpC, hpD, hg.symm, hgbase, ?_⟩
  apply hZ.hom_ext
  · exact factor_model_triangle g a jY f qW qZ qA qY c i j qAT qYT pC pD e
      hg hpC hpD ha hj hf he
  · exact factor_base_triangle g a jY f a₀ y₀ w₀ z₀ hgbase habase hjbase hfbase

end SchubertGeometry
