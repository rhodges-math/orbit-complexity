import OrbitComplexity.SchubertGeometry.Connectedness.CellArithmeticConnected
import OrbitComplexity.SchubertGeometry.Connectedness.ContractionRetention
import OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointConnected
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.CoefficientAwayStage
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Connected arithmetic Richardson targets

Cell contractions and reflection curves give connected fibres after a
coefficient enlargement and a principal localization. The localization is
realized inside the ambient field, and the prescribed target comparison is
retained on the resulting coefficient stage.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u

namespace SchubertGeometry

open private stage_map stage_map_cartesian stage_map_original scalar_fp scalar_qc
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected
open private coefficient_comp
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointConnected

private def scalar_over_iso {B T : Scheme.{u}} (κ : T ⟶ B) (X : Over B) :
    Over.mk (pullback.fst κ X.hom) ≅ (Over.pullback κ).obj X :=
  Over.isoMk (pullbackSymmetry κ X.hom) (by simp)

private theorem gc_of_over_iso {B : Scheme.{u}} {X Y : Over B}
    (E : X ≅ Y) (h : GeometricallyConnected Y.hom) :
    GeometricallyConnected X.hom :=
  E.hom.w ▸ (MorphismProperty.cancel_left_of_respectsIso
    (@GeometricallyConnected) E.hom.left Y.hom).mpr h

private theorem scalar_three_gc {B R T A : Scheme.{u}}
    (κ : R ⟶ B) (τ : T ⟶ R) (β : A ⟶ T) (δ : A ⟶ B)
    (hδ : β ≫ τ ≫ κ = δ) (X : Over B)
    (h : GeometricallyConnected
      ((Over.pullback β).obj
        (Over.mk (pullback.fst τ (pullback.fst κ X.hom)))).hom) :
    GeometricallyConnected (Over.mk (pullback.fst δ X.hom)).hom := by
  subst δ
  let X₁ : Over R := Over.mk (pullback.fst κ X.hom)
  let F := Over.pullback β
  let E := scalar_over_iso (β ≫ τ ≫ κ) X ≪≫
    (Over.pullbackComp β (τ ≫ κ)).app X ≪≫
    F.mapIso ((Over.pullbackComp τ κ).app X) ≪≫
    F.mapIso ((Over.pullback τ).mapIso (scalar_over_iso κ X).symm ≪≫
      (scalar_over_iso τ X₁).symm)
  exact gc_of_over_iso E h

private theorem arithmetic_square {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (X : Over (Spec (.of S)))
    {XK : Scheme.{u}} (aK : XK ⟶ Spec (.of K)) (q : XK ⟶ X.left)
    (h : IsPullback q aK X.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (k : CoefficientStage S) :
    ∃ qk : XK ⟶ (stageScalarModel S X.hom k).left,
      IsPullback qk aK (stageScalarModel S X.hom k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
      qk ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
        X.hom = q := by
  exact ⟨stage_map S X (Over.mk aK) q h k,
    stage_map_cartesian S X (Over.mk aK) q h k,
    stage_map_original S X (Over.mk aK) q h k⟩

/-- A prescribed model of a nonempty Richardson variety has geometrically
connected fibres after enlarging its coefficient subalgebra above a given
stage. The Cartesian comparison and its projection to the original target
are retained. -/
theorem exists_richardson_model_connected {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : G.weylGroup)
    (hab : WeylBruhatLE G.rootBase a b)
    (S : Subalgebra ℤ K)
    (D : Over (Spec (.of S)))
    [LocallyOfFinitePresentation D.hom] [QuasiCompact D.hom]
    (qD : (richardsonVariety G a b).scheme ⟶ D.left)
    (hD : IsPullback qD (richardsonVariety G a b).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k),
      GeometricallyConnected (stageScalarModel S D.hom k).hom ∧
      ∃ qk : (richardsonVariety G a b).scheme ⟶ (stageScalarModel S D.hom k).left,
        IsPullback qk (richardsonVariety G a b).toSpec
          (stageScalarModel S D.hom k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
        qk ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
          D.hom = qD := by
  classical
  obtain ⟨R, hstartR, hR, ⟨M⟩⟩ :=
    CellContraction.exists_cell_contraction_models (G := G) a b
      start.val start.property.1
  let kR : CoefficientStage S :=
    ⟨R, hR, start.property.2.trans hstartR⟩
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion kR.property.2).toRingHom)
  let DR := stageScalarModel S D.hom kR
  let : LocallyOfFinitePresentation DR.hom := scalar_fp κ D
  let : QuasiCompact DR.hom := scalar_qc κ D
  obtain ⟨qR, hDR, _hOriginalR⟩ :=
    arithmetic_square S D (richardsonVariety G a b).toSpec qD hD kR
  obtain ⟨k, _hk, r, hr, hConnected⟩ :=
    CellContraction.exists_cellArithmetic_connected (G := G) (R := R)
      a b hab hR M DR qR hDR ⟨R, hR, le_rfl⟩
  obtain ⟨T, hKT, hT, hAway⟩ :=
    exists_coefficient_away k.val k.property.1 r hr
  let : Algebra k.val T := (Subalgebra.inclusion hKT).toAlgebra
  let : IsLocalization.Away r T := hAway
  let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let β := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hKT).toRingHom)
  let hST := (kR.property.2.trans k.property.2).trans hKT
  let kT : CoefficientStage S := ⟨T, hT, hST⟩
  let δ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom)
  have hδ : β ≫ τ ≫ κ = δ :=
    (congrArg (fun t => β ≫ t) (coefficient_comp kR.property.2 k.property.2)).trans
      (coefficient_comp (kR.property.2.trans k.property.2) hKT)
  have hlocal := hConnected T
  have hgc := scalar_three_gc κ τ β δ hδ D hlocal
  obtain ⟨qT, hDT, hOriginalT⟩ :=
    arithmetic_square S D (richardsonVariety G a b).toSpec qD hD kT
  exact ⟨kT, (hstartR.trans k.property.2).trans hKT, hgc, qT, hDT, hOriginalT⟩

end SchubertGeometry
