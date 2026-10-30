import OrbitComplexity.FrobeniusSplitting.Normality.Limits.SmoothSchemeStages
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Smooth stages with a prescribed Cartesian comparison

Smoothness is transported through an isomorphism over the field before applying
the coefficient-stage theorem. Both the new Cartesian comparison and its
projection to the initial model are retained.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace FrobeniusSplitting

universe u

open private model_scalar_original
  from OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian

private theorem overIso_smooth {B : Scheme.{u}} {X Y : Over B}
    (E : X ≅ Y) [Smooth X.hom] : Smooth Y.hom := by
  have h : Smooth (E.inv.left ≫ X.hom) := inferInstance
  exact (Over.w E.inv) ▸ h

private theorem projection_comp {C : Type*} [Category C]
    {A B D E : C} (e : A ⟶ B) (v : B ⟶ D) (r : D ⟶ E)
    (q : B ⟶ E) (f : A ⟶ E) (hv : v ≫ r = q) (he : e ≫ q = f) :
    (e ≫ v) ≫ r = f := by
  rw [Category.assoc, hv, he]

/-- A Cartesian model of a smooth field scheme becomes smooth above any
prescribed coefficient stage, with its initial projection retained. -/
theorem exists_smooth_cartesian_stage {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG)
    (F : Over (Spec (.of S))) [CompactSpace F.left]
    [LocallyOfFinitePresentation F.hom]
    (X : Over (Spec (.of K))) [Smooth X.hom]
    (q : X.left ⟶ F.left)
    (hq : IsPullback q X.hom F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    ∃ t : CoefficientStage S, start ≤ t ∧
      Smooth (stageScalarModel S F.hom t).hom ∧
      ∃ qt : X.left ⟶ (stageScalarModel S F.hom t).left,
        IsPullback qt X.hom (stageScalarModel S F.hom t).hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
        qt ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom
            (Subalgebra.inclusion t.property.2).toRingHom)) F.hom = q := by
  let E : X ≅ genericScalarModel S F.hom := hq.flip.isoOverPullback
  let : Smooth (genericScalarModel S F.hom).hom := overIso_smooth E
  obtain ⟨t, ht, hs⟩ := exists_smooth_scalar_stage S hS F start
  let qt : X.left ⟶ (stageScalarModel S F.hom t).left :=
    E.hom.left ≫ (modelScalarCone S F.hom).π.app (op t)
  refine ⟨t, ht, hs, qt, overIso_modelStage_cartesian S F.hom t X E, ?_⟩
  exact projection_comp E.hom.left ((modelScalarCone S F.hom).π.app (op t))
    (pullback.snd
      (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion t.property.2).toRingHom)) F.hom)
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) F.hom)
    q (model_scalar_original S F.hom t)
    hq.flip.isoOverPullback_hom_left_comp_snd

end FrobeniusSplitting
