import OrbitComplexity.SchubertGeometry.Connectedness.TargetStageObjects
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coefficient transport for closed targets

An isomorphism of ambient models transports each closed inclusion and its
Cartesian comparison. The equation with the original ambient projection
persists through the coefficient change.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting

noncomputable section
universe u v

namespace SchubertGeometry

open private closed_target_stage
  from OrbitComplexity.SchubertGeometry.Connectedness.TargetStageObjects

private theorem cartesian_target_iso {C : Type v} [Category C]
    {A X Y S T : C} (q : A ⟶ X) (a : A ⟶ S) (b : X ⟶ T)
    (c : Y ⟶ T) (ρ : S ⟶ T) (E : X ≅ Y)
    (he : E.hom ≫ c = b) (h : IsPullback q a b ρ) :
    IsPullback (q ≫ E.hom) a c ρ := by
  have hi : IsPullback E.hom b c (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using he⟩
  simpa only [Category.comp_id] using h.paste_horiz hi

private theorem projection_after_iso {C : Type v} [Category C]
    {A X Y B Z : C} (q : A ⟶ X) (e : X ⟶ Y)
    (c : Y ⟶ Z) (b : X ⟶ B) (p : B ⟶ Z)
    (q₀ : A ⟶ B) (qP : A ⟶ Z)
    (he : e ≫ c = b ≫ p) (hq : q ≫ b = q₀) (h₀ : q₀ ≫ p = qP) :
    (q ≫ e) ≫ c = qP := by
  calc
    (q ≫ e) ≫ c = q ≫ (e ≫ c) := Category.assoc _ _ _
    _ = q ≫ (b ≫ p) := congrArg (fun z => q ≫ z) he
    _ = (q ≫ b) ≫ p := (Category.assoc _ _ _).symm
    _ = q₀ ≫ p := congrArg (fun z => z ≫ p) hq
    _ = qP := h₀

private theorem triangle_after_iso {C : Type v} [Category C]
    {X A Y B D : C} (qX : X ⟶ A) (i : A ⟶ B)
    (j : X ⟶ Y) (qY : Y ⟶ B) (e : B ⟶ D)
    (h : qX ≫ i = j ≫ qY) :
    qX ≫ (i ≫ e) = j ≫ (qY ≫ e) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ e) h).trans (Category.assoc _ _ _))

private theorem merge_target_stage {K : Type u} [CommRing K] {I : Type v}
    (S T : Subalgebra ℤ K) (hST : S ≤ T)
    (Y : Over (Spec (.of K))) (X : I → Over (Spec (.of K)))
    (j : ∀ i, X i ⟶ Y)
    (P : Over (Spec (.of S))) (PT : Over (Spec (.of T)))
    (p : PT.left ⟶ P.left) (qP : Y.left ⟶ P.left) (qT : Y.left ⟶ PT.left)
    (hOriginal : qT ≫ p = qP)
    (start : CoefficientStage S) (startT : CoefficientStage T)
    (hstart : start.val ≤ T)
    (hdata : closed_target_stage T Y X j PT qT startT)
    (flat : ∀ r : CoefficientStage T,
      ∃ E : stageScalarModel T PT.hom r ≅
          stageScalarModel S P.hom ⟨r.val, r.property.1, hST.trans r.property.2⟩,
        E.hom.left ≫ pullback.snd
            (Spec.map (CommRingCat.ofHom
              (Subalgebra.inclusion (hST.trans r.property.2)).toRingHom)) P.hom =
          pullback.snd
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom))
            PT.hom ≫ p) :
    closed_target_stage S Y X j P qP start := by
  obtain ⟨r, _hr, D, iD, qF, qD, hF, hOld, hD⟩ := hdata
  obtain ⟨E, hE⟩ := flat r
  let k : CoefficientStage S := ⟨r.val, r.property.1, hST.trans r.property.2⟩
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom)
  have hCart : IsPullback (qF ≫ E.hom.left) Y.hom (stageScalarModel S P.hom k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) :=
    cartesian_target_iso qF Y.hom (stageScalarModel T PT.hom r).hom
      (stageScalarModel S P.hom k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K)))
      ((Over.forget _).mapIso E) E.hom.w hF
  have hProjection : (qF ≫ E.hom.left) ≫ pullback.snd κ P.hom = qP :=
    projection_after_iso qF E.hom.left (pullback.snd κ P.hom)
      (pullback.snd τ PT.hom) p qT qP hE hOld hOriginal
  refine ⟨k, hstart.trans r.property.2, D, (fun i => iD i ≫ E.hom),
    qF ≫ E.hom.left, qD, hCart, hProjection, ?_⟩
  intro i
  rcases hD i with ⟨hClosed, hCartD, hTriangle, hfp, hcompact, hqs⟩
  let : IsClosedImmersion (iD i).left := hClosed
  have hClosed' : IsClosedImmersion (iD i ≫ E.hom).left :=
    inferInstanceAs (IsClosedImmersion ((iD i).left ≫ E.hom.left))
  exact ⟨hClosed', hCartD,
    triangle_after_iso (qD i) (iD i).left (j i).left qF E.hom.left hTriangle,
    hfp, hcompact, hqs⟩

end SchubertGeometry
