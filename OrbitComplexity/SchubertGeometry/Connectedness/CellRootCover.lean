import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.CellRootDiagram
import OrbitComplexity.SchubertGeometry.Connectedness.CellCoverRetention
import OrbitComplexity.SchubertGeometry.Connectedness.CellMapProperties
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian

set_option autoImplicit false

/-! # A principal-open cover for the cell and root-curve diagram

The cell maps, root curves and endpoint incidences are kept at the same
coefficient stage. Their cell images cover the chosen target over one
nonempty principal open of the coefficient base.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
  ReductiveGroups FrobeniusSplitting GroupActions

namespace SchubertGeometry.CellContraction

universe u v

private theorem add_cover_witness
    {J : Type*} {A : J → Type*} {B : J → Type*} {C : J → Type*}
    (L : J → Prop) (P : ∀ j, A j → Prop)
    (Q : ∀ j, A j → B j → C j → Prop) (W : ∀ j, A j → Prop)
    (h : ∃ (j : J) (_ : L j) (a : A j) (b : B j) (c : C j),
      P j a ∧ Q j a b c)
    (hw : ∀ j a, P j a → W j a) :
    ∃ (j : J) (_ : L j) (a : A j) (b : B j) (c : C j),
      P j a ∧ Q j a b c ∧ W j a := by
  obtain ⟨j, hj, a, b, c, hp, hq⟩ := h
  exact ⟨j, hj, a, b, c, hp, hq, hw j a hp⟩

private theorem stage_target_properties {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    [LocallyOfFinitePresentation a] [QuasiCompact a] (k : CoefficientStage S) :
    LocallyOfFinitePresentation (stageScalarModel S a k).hom ∧
      QuasiCompact (stageScalarModel S a k).hom ∧
      CompactSpace (stageScalarModel S a k).left ∧
      QuasiSeparatedSpace (stageScalarModel S a k).left := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let : LocallyOfFinitePresentation (stageScalarModel S a k).hom := by
    change LocallyOfFinitePresentation (pullback.fst κ a)
    infer_instance
  let : QuasiCompact (stageScalarModel S a k).hom := by
    change QuasiCompact (pullback.fst κ a)
    infer_instance
  have hc : CompactSpace (stageScalarModel S a k).left :=
    QuasiCompact.compactSpace_of_compactSpace (stageScalarModel S a k).hom
  let : Algebra.FiniteType ℤ k.val :=
    (Subalgebra.fg_iff_finiteType k.val).mp k.property.1
  let : IsNoetherianRing k.val := Algebra.FiniteType.isNoetherianRing ℤ k.val
  let : IsLocallyNoetherian (stageScalarModel S a k).left :=
    LocallyOfFiniteType.isLocallyNoetherian (stageScalarModel S a k).hom
  exact ⟨inferInstance, inferInstance, hc, inferInstance⟩

attribute [local instance] coefficientAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (R : Subalgebra ℤ K)

private theorem cover_from_comparisons (a b : G.weylGroup)
    (S : Subalgebra ℤ K) (Y : Over (Spec (.of S)))
    (hc : CompactSpace Y.left) (hqs : QuasiSeparatedSpace Y.left)
    (hfp : LocallyOfFinitePresentation Y.hom) (hqc : QuasiCompact Y.hom)
    (X : cellPieceIndices G a b → Over (Spec (.of S)))
    (f : ∀ t : cellPieceIndices G a b, X t ⟶ Y)
    (hmaps : ∀ t, LocallyOfFinitePresentation (f t).left ∧ QuasiCompact (f t).left)
    (qX : ∀ t : cellPieceIndices G a b, (cellIntersection G a b t.val).left ⟶ (X t).left)
    (qY : (richardsonVariety G a b).scheme ⟶ Y.left)
    (hsq : IsPullback qY (richardsonVariety G a b).toSpec Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hcomm : ∀ t : cellPieceIndices G a b, qX t ≫ (f t).left =
      (pullback.snd (schubertCellInclusion G t.val) (richardsonInclusion G a b)).left ≫ qY) :
    ∃ r : S, r ≠ 0 ∧ ∀ y : Y.left, Y.hom y ∈ PrimeSpectrum.basicOpen r →
      ∃ t x, (f t).left x = y := by
  let : CompactSpace Y.left := hc
  let : QuasiSeparatedSpace Y.left := hqs
  let : LocallyOfFinitePresentation Y.hom := hfp
  let : QuasiCompact Y.hom := hqc
  let : ∀ t, LocallyOfFinitePresentation (f t).left := fun t => (hmaps t).1
  let : ∀ t, QuasiCompact (f t).left := fun t => (hmaps t).2
  exact exists_cell_cover_open G a b S (D := Y.left) Y.hom
    (fun t => (X t).left) (fun t => (f t).left) qX qY hsq hcomm

/-- The cell and reflection-root diagram is retained on one stage whose cell
images cover the chosen target over a nonempty principal open of its base. -/
theorem exists_cell_root_cover (a b : G.weylGroup) (hR : R.FG)
    (M : ∀ t : {t : G.weylGroup // Nonempty (cellIntersection G a b t).left},
      ArithmeticContractionModel (R := R)
        (cellContractionAlg G a b t.val) (cellOriginAlg G a b t.val t.property))
    {I : Type v} [Fintype I] (w : I → G.weylGroup)
    (i : I → G.rootBase.support) (x : I → G.weylGroup)
    (hroot : ∀ z, G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm (w z) (i z).val))
    (hpos : ∀ z, G.rootBase.IsPos (G.rootSystem.weylGroupToPerm (x z)⁻¹
      (G.rootSystem.weylGroupToPerm (w z) (i z).val)))
    (hax : ∀ z, WeylBruhatLE G.rootBase a (x z))
    (hxy : ∀ z, WeylBruhatLE G.rootBase (x z)
      (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm (w z) (i z).val) * x z))
    (hyb : ∀ z, WeylBruhatLE G.rootBase
      (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm (w z) (i z).val) * x z) b)
    (hne₀ : ∀ z, Nonempty (cellIntersection G a b (x z)).left)
    (hne₁ : ∀ z, Nonempty (cellIntersection G a b
      (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm (w z) (i z).val) * x z)).left)
    (D : Over (Spec (.of R))) [LocallyOfFinitePresentation D.hom] [QuasiCompact D.hom]
    (qD : (richardsonVariety G a b).scheme ⟶ D.left)
    (hD : IsPullback qD (richardsonVariety G a b).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (start : CoefficientStage R) :
    let vertex : I × Bool → {t : G.weylGroup // Nonempty (cellIntersection G a b t).left} :=
      fun r => if r.2 then
        ⟨RootPairing.weylGroup.ofIdx G.rootSystem
          (G.rootSystem.weylGroupToPerm (w r.1) (i r.1).val) * x r.1, hne₁ r.1⟩
      else ⟨x r.1, hne₀ r.1⟩
    ∃ (k : CoefficientStage R) (_ : start ≤ k)
      (f : ∀ t : {t : G.weylGroup // Nonempty (cellIntersection G a b t).left},
        stageScalarModel R (cellArithmeticBase G a b t.val t.property (M t)) k ⟶
          stageScalarModel R D.hom k)
      (s : ∀ _r : I × Bool, stageScalarModel R (𝟙 (Spec (.of R))) k ⟶
        stageScalarModel R (projectiveToSpec R (ULift.{u} (Fin 2))) k)
      (c : ∀ _z : I, stageScalarModel R (projectiveToSpec R (ULift.{u} (Fin 2))) k ⟶
        stageScalarModel R D.hom k),
      (∀ t : {t : G.weylGroup // Nonempty (cellIntersection G a b t).left},
        ((modelScalarCone R (cellArithmeticBase G a b t.val t.property (M t))).π.app
            (op k) ≫ (f t).left =
          (cellArithmeticMap G a b t.val t.property (M t) D.hom qD hD).left ≫
            (modelScalarCone R D.hom).π.app (op k)) ∧
        ((((cellArithmeticGenericIso G a b t.val t.property (M t)).inv.left ≫
            (modelScalarCone R (cellArithmeticBase G a b t.val t.property (M t))).π.app
              (op k)) ≫ (f t).left =
          (pullback.snd (schubertCellInclusion G t.val) (richardsonInclusion G a b)).left ≫
            (chosenGenericIso R (richardsonVariety G a b).toOver D.hom qD hD).hom.left ≫
              (modelScalarCone R D.hom).π.app (op k))) ∧
        ((modelScalarCone R (𝟙 (Spec (.of R)))).π.app (op k) ≫
            (cellArithmeticAnchorMap G a b t.val t.property (M t) D k (f t)).left =
          (cellAnchorGenericMap G a b t.val t.property R D qD hD).left ≫
            (modelScalarCone R D.hom).π.app (op k))) ∧
      (∀ r : I × Bool,
        s r ≫ c r.1 = cellArithmeticAnchorMap G a b
          (vertex r).val (vertex r).property (M (vertex r)) D k (f (vertex r)) ∧
        (modelScalarCone R (𝟙 (Spec (.of R)))).π.app (op k) ≫ (s r).left =
          (rootEndpointGenericMap R r.2).left ≫
            (modelScalarCone R (projectiveToSpec R (ULift.{u} (Fin 2)))).π.app (op k) ∧
        (modelScalarCone R (projectiveToSpec R (ULift.{u} (Fin 2)))).π.app (op k) ≫
            (c r.1).left =
          (projectiveGenericMap R (ULift.{u} (Fin 2)) D (richardsonVariety G a b).toOver
            qD hD (rootCurveRichardson G (w r.1) (i r.1) a (x r.1) b
              (hroot r.1) (hpos r.1) (hax r.1) (hxy r.1) (hyb r.1))).left ≫
            (modelScalarCone R D.hom).π.app (op k)) ∧
      ∃ r : k.val, r ≠ 0 ∧ ∀ y : (stageScalarModel R D.hom k).left,
        (stageScalarModel R D.hom k).hom y ∈ PrimeSpectrum.basicOpen r →
          ∃ (t : {t : G.weylGroup // Nonempty (cellIntersection G a b t).left})
            (z : (stageScalarModel R
              (cellArithmeticBase G a b t.val t.property (M t)) k).left),
            (f t).left z = y := by
  refine add_cover_witness _ _ _ _
    (exists_cell_root_diagram G R a b hR M w i x hroot hpos hax hxy hyb hne₀ hne₁
      D qD hD start) ?_
  intro k f hf
  have hprops := stage_target_properties R D.hom k
  let qX : ∀ t : cellPieceIndices G a b, (cellIntersection G a b t.val).left ⟶
      (stageScalarModel R (cellArithmeticBase G a b t.val t.property (M t)) k).left :=
    fun (t : cellPieceIndices G a b) =>
      (cellArithmeticGenericIso G a b t.val t.property (M t)).inv.left ≫
        (modelScalarCone R (cellArithmeticBase G a b t.val t.property (M t))).π.app (op k)
  let qY : (richardsonVariety G a b).scheme ⟶ (stageScalarModel R D.hom k).left :=
    (chosenGenericIso R (richardsonVariety G a b).toOver D.hom qD hD).hom.left ≫
      (modelScalarCone R D.hom).π.app (op k)
  have hcart : IsPullback qY (richardsonVariety G a b).toSpec
      (stageScalarModel R D.hom k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) :=
    overIso_modelStage_cartesian R D.hom k (richardsonVariety G a b).toOver
      (chosenGenericIso R (richardsonVariety G a b).toOver D.hom qD hD)
  have hmaps : ∀ t : cellPieceIndices G a b,
      LocallyOfFinitePresentation (f t).left ∧ QuasiCompact (f t).left :=
    fun (t : cellPieceIndices G a b) =>
      cellStageMap_finitePres G a b t.val t.property (M t) D k (f t)
  have hcomm : ∀ t : cellPieceIndices G a b, qX t ≫ (f t).left =
      (pullback.snd (schubertCellInclusion G t.val) (richardsonInclusion G a b)).left ≫ qY :=
    fun (t : cellPieceIndices G a b) => (hf t).2.1
  exact cover_from_comparisons G a b k.val (stageScalarModel R D.hom k)
    hprops.2.2.1 hprops.2.2.2 hprops.1 hprops.2.1
    (fun (t : cellPieceIndices G a b) =>
      stageScalarModel R (cellArithmeticBase G a b t.val t.property (M t)) k)
    f hmaps qX qY hcart hcomm

end SchubertGeometry.CellContraction
