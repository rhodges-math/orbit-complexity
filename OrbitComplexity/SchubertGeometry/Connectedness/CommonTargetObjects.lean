import OrbitComplexity.SchubertGeometry.Connectedness.TargetStageTransport
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixCommonCoefficients
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Closed targets on the original coefficient model

The coordinate constructions choose several intermediate coefficient
rings. Their closed target objects are transported back to one scalar
extension of the prescribed ambient model, retaining its original map.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting

noncomputable section
universe u

namespace SchubertGeometry

open private closed_target_stage target_objects
  from OrbitComplexity.SchubertGeometry.Connectedness.TargetStageObjects
open private merge_target_stage
  from OrbitComplexity.SchubertGeometry.Connectedness.TargetStageTransport
open private common_targets
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixCommonCoefficients
open private coefficient_targets
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixStageCoordinates
open private scalar_functor
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendCellConnected

private theorem common_objects
    {Y : Scheme.{u}} {J I K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (X : I → Scheme.{u}) [∀ i, IsAffineHom (pullback.diagonal (terminal.from (X i)))]
    (j : ∀ i, X i ⟶ Y) [∀ i, IsClosedImmersion (j i)]
    (base : Y ⟶ Spec (.of K)) (U : J → Y.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (S₀ : Subalgebra ℤ K) (P : Over (Spec (.of S₀))) (qF : Y ⟶ P.left)
    (start₀ : CoefficientStage S₀)
    (hdata : common_targets X j base U hU S₀ P qF start₀) :
    closed_target_stage S₀ (Over.mk base)
      (fun i => Over.mk (j i ≫ base)) (fun i => Over.homMk (j i) rfl) P qF start₀ := by
  obtain ⟨S, N, e, β, T, h₀, hSTraw, hstart, hT, hRest⟩ := hdata
  let : Algebra S T := (Subalgebra.inclusion hSTraw).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hSTraw K
  let : Algebra S₀ T := (Subalgebra.inclusion h₀).toAlgebra
  let : IsScalarTower S₀ T K := Subalgebra.inclusion.isScalarTower_right h₀ K
  let κ₀ := Spec.map (CommRingCat.ofHom (algebraMap S₀ T))
  let PT := (scalar_functor κ₀).obj P
  obtain ⟨qT, _hCartT, _hBaseT, hOriginalT, _hCoeffT, ⟨k, hCoeff⟩, hFlatT⟩ := hRest
  let : Algebra T k.val := (Subalgebra.inclusion k.property.2).toAlgebra
  let : IsScalarTower T k.val K :=
    Subalgebra.inclusion.isScalarTower_right k.property.2 K
  let κ₁ := Spec.map (CommRingCat.ofHom (algebraMap T k.val))
  let Pk := (scalar_functor κ₁).obj PT
  obtain ⟨qPk, _hCartPk, _hnF, _hnB, _hBasePk, hOriginalPk,
    _hCoeffPk, hResult, hFlatK⟩ := hCoeff
  have hClosed : closed_target_stage k.val (Over.mk base)
      (fun i => Over.mk (j i ≫ base)) (fun i => Over.homMk (j i) rfl)
      Pk qPk ⟨k.val, k.property.1, le_rfl⟩ :=
    target_objects (hdata := hResult)
  have flatK : ∀ r : CoefficientStage k.val,
      ∃ E : stageScalarModel k.val Pk.hom r ≅
          stageScalarModel T PT.hom
            ⟨r.val, r.property.1, k.property.2.trans r.property.2⟩,
        E.hom.left ≫ pullback.snd
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion
              (k.property.2.trans r.property.2)).toRingHom)) PT.hom =
          pullback.snd
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom))
            Pk.hom ≫ pullback.snd κ₁ PT.hom := by
    intro r
    let : Algebra T r.val :=
      (Subalgebra.inclusion (k.property.2.trans r.property.2)).toAlgebra
    let : Algebra k.val r.val := (Subalgebra.inclusion r.property.2).toAlgebra
    let : IsScalarTower T k.val r.val := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    obtain ⟨E, _hfst, hOld⟩ := hFlatK r.val
    exact ⟨E, hOld⟩
  have hAtT := merge_target_stage T k.val k.property.2 (Over.mk base)
    (fun i => Over.mk (j i ≫ base)) (fun i => Over.homMk (j i) rfl)
    PT Pk (pullback.snd κ₁ PT.hom) qT qPk hOriginalPk
    ⟨T, hT, le_rfl⟩ ⟨k.val, k.property.1, le_rfl⟩ k.property.2 hClosed flatK
  have flatT : ∀ r : CoefficientStage T,
      ∃ E : stageScalarModel T PT.hom r ≅
          stageScalarModel S₀ P.hom ⟨r.val, r.property.1, h₀.trans r.property.2⟩,
        E.hom.left ≫ pullback.snd
            (Spec.map (CommRingCat.ofHom
              (Subalgebra.inclusion (h₀.trans r.property.2)).toRingHom)) P.hom =
          pullback.snd
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom))
            PT.hom ≫ pullback.snd κ₀ P.hom := by
    intro r
    let : Algebra S₀ r.val := (Subalgebra.inclusion (h₀.trans r.property.2)).toAlgebra
    let : Algebra T r.val := (Subalgebra.inclusion r.property.2).toAlgebra
    let : IsScalarTower S₀ T r.val := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    obtain ⟨E, _hfst, hOld⟩ := hFlatT r.val
    exact ⟨E, hOld⟩
  exact merge_target_stage S₀ T h₀ (Over.mk base)
    (fun i => Over.mk (j i ≫ base)) (fun i => Over.homMk (j i) rfl)
    P PT (pullback.snd κ₀ P.hom) qF qT hOriginalT start₀ ⟨T, hT, le_rfl⟩
    hstart hAtT flatT

end SchubertGeometry
