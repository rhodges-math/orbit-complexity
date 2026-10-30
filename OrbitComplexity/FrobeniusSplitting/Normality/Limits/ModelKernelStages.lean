import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares
import Batteries.Tactic.Lint

/-! # Closed model ideals at coefficient stages -/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FrobeniusSplitting

/-- An isomorphism commuting with arrows after a Cartesian ambient projection
identifies the ideals of those arrows. -/
theorem model_kernel_eq
    {B T : Scheme.{u}} (κ : T ⟶ B)
    {C D F : Over B} {C' D' F' : Over T}
    (E : C' ≅ D') (i : C ⟶ F) (j : D ⟶ F)
    (i' : C' ⟶ F') (j' : D' ⟶ F')
    (qC : C'.left ⟶ C.left) (qD : D'.left ⟶ D.left)
    (qF : F'.left ⟶ F.left)
    (hF : IsPullback qF F'.hom F.hom κ)
    (hi : i'.left ≫ qF = qC ≫ i.left)
    (hj : j'.left ≫ qF = qD ≫ j.left)
    (hE : E.hom.left ≫ qD ≫ j.left = qC ≫ i.left) :
    i'.left.ker = j'.left.ker := by
  have h : E.hom.left ≫ j'.left = i'.left := by
    apply hF.hom_ext
    · calc
        _ = E.hom.left ≫ (j'.left ≫ qF) := Category.assoc _ _ _
        _ = E.hom.left ≫ (qD ≫ j.left) := by rw [hj]
        _ = qC ≫ i.left := hE
        _ = _ := hi.symm
    · calc
        _ = E.hom.left ≫ D'.hom := by rw [Category.assoc, j'.w]
        _ = C'.hom := E.hom.w
        _ = _ := i'.w.symm
  calc
    i'.left.ker = (E.hom.left ≫ j'.left).ker := congrArg Scheme.Hom.ker h.symm
    _ = j'.left.ker := Scheme.Hom.ker_comp_of_isIso _ _

/-- Equality of closed ideals on the scalar fibre holds for the corresponding
closed models after increasing the coefficient ring above any given stage. -/
theorem exists_closed_model_kernel_stage
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    (C D F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [CompactSpace D.left] [QuasiSeparatedSpace D.left]
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation D.hom]
    [LocallyOfFiniteType F.hom] (i : C ⟶ F) (j : D ⟶ F)
    (X Y Z : Over (Spec (.of K))) (iK : X ⟶ Z) (jK : Y ⟶ Z)
    [IsClosedImmersion iK.left] [IsClosedImmersion jK.left]
    (qX : X.left ⟶ C.left) (qY : Y.left ⟶ D.left) (qZ : Z.left ⟶ F.left)
    (hX : IsPullback qX X.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY Y.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hi : iK.left ≫ qZ = qX ≫ i.left) (hj : jK.left ≫ qZ = qY ≫ j.left)
    (hker : iK.left.ker = jK.left.ker) (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t),
      ∀ (it : stageScalarModel S C.hom t ⟶ stageScalarModel S F.hom t)
        (jt : stageScalarModel S D.hom t ⟶ stageScalarModel S F.hom t),
      it.left ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          F.hom =
        pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          C.hom ≫ i.left →
      jt.left ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          F.hom =
        pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          D.hom ≫ j.left →
      it.left.ker = jt.left.ker := by
  obtain ⟨t, ht, E, hE⟩ := exists_closed_ideal_iso_stage S hS C D F i j
    X Y Z iK jK qX qY qZ hX hY hi hj hker start
  refine ⟨t, ht, ?_⟩
  intro it jt hit hjt
  exact model_kernel_eq
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
    E i j it jt (pullback.snd _ C.hom) (pullback.snd _ D.hom)
    (pullback.snd _ F.hom) (IsPullback.of_hasPullback _ F.hom).flip hit hjt hE

end FrobeniusSplitting
