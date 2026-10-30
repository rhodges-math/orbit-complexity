import OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointArrows
import OrbitComplexity.SchubertGeometry.Parabolics.Projection
import OrbitComplexity.FrobeniusSplitting.Normality.FiniteArithmeticSchemes
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Arithmetic partial-flag projections

A finite family of the complete-to-partial flag projections descends from the
same chosen flag model. The comparisons retain its original scalar projection,
and each projection square is Cartesian.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting

namespace SchubertGeometry

universe u v

open private finite_coefficient_upper coefficient_triangle source_scalar_square
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointModels
open private cartesian_over_iso retained_iso_square retained_original two_projections
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointArrows

private theorem variety_affine_diagonal
    {K : Type u} [Field K] (V : GroupActions.Variety K) :
    IsAffineHom (pullback.diagonal (terminal.from V.scheme)) := by
  let : IsSeparated (terminal.from V.scheme) := by
    rw [← terminal.comp_from V.toSpec]
    infer_instance
  let : IsClosedImmersion (pullback.diagonal (terminal.from V.scheme)) :=
    IsSeparated.isClosedImmersion_diagonal (f := terminal.from V.scheme)
  infer_instance

private def scalar_stage_map
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (X : Over (Spec (.of K))) (A : Over (Spec (.of S)))
    (E : X ≅ genericScalarModel S A.hom) (k : CoefficientStage S) :
    X.left ⟶ (stageScalarModel S A.hom k).left :=
  E.hom.left ≫ (modelScalarCone S A.hom).π.app (op k)

private theorem cartesian_arrow_square
    {B BK : Scheme.{u}} (ρ : BK ⟶ B)
    {X Y : Over BK} {A Q : Over B} (f : X ⟶ Y) (π : A ⟶ Q)
    (qX : X.left ⟶ A.left) (qY : Y.left ⟶ Q.left)
    (hX : IsPullback qX X.hom A.hom ρ)
    (hY : IsPullback qY Y.hom Q.hom ρ)
    (h : qX ≫ π.left = f.left ≫ qY) :
    IsPullback f.left qX qY π.left := by
  have houter : IsPullback (f.left ≫ Y.hom) qX ρ (π.left ≫ Q.hom) := by
    rw [f.w, π.w]
    exact hX.flip
  exact houter.of_right h.symm hY.flip

private theorem flag_arrow_properties
    {B : Scheme.{u}} [IsLocallyNoetherian B] [CompactSpace B]
    {A Q : Over B} [LocallyOfFinitePresentation A.hom] [QuasiCompact A.hom]
    [IsSeparated A.hom] [LocallyOfFinitePresentation Q.hom] (π : A ⟶ Q) :
    LocallyOfFinitePresentation π.left ∧ QuasiCompact π.left ∧ IsSeparated π.left := by
  have : IsLocallyNoetherian Q.left := LocallyOfFiniteType.isLocallyNoetherian Q.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : LocallyOfFiniteType (π.left ≫ Q.hom) := by
    rw [π.w]
    infer_instance
  have : LocallyOfFiniteType π.left := locallyOfFiniteType_of_comp π.left Q.hom
  have : IsSeparated (π.left ≫ Q.hom) := by
    rw [π.w]
    infer_instance
  exact ⟨inferInstance, inferInstance, IsSeparated.of_comp π.left Q.hom⟩

/-- Finitely many complete-to-partial projections have arithmetic models from
one scalar extension of the prescribed flag model. The projection
squares are Cartesian, and all projections are finitely presented,
quasi-compact and separated. -/
theorem exists_word_partial_flags
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {I : Type v} [Finite I] (G : ReductiveGroupData K) (s : I → G.rootBase.support)
    (S : Subalgebra ℤ K) (start : CoefficientStage S)
    (F : Over (Spec (.of S)))
    [LocallyOfFinitePresentation F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k) (l : CoefficientStage k.val)
      (Q : I → Over (Spec (.of l.val)))
      (π : ∀ i, stageScalarModel k.val (stageScalarModel S F.hom k).hom l ⟶ Q i)
      (mF : (flagVariety G).scheme ⟶
        (stageScalarModel k.val (stageScalarModel S F.hom k).hom l).left)
      (mQ : ∀ i, (partialFlagVariety G {s i}).scheme ⟶ (Q i).left),
      mF ≫ pullback.snd _ (stageScalarModel S F.hom k).hom ≫
        pullback.snd _ F.hom = qF ∧
      IsPullback mF (flagVariety G).toSpec
        (stageScalarModel k.val (stageScalarModel S F.hom k).hom l).hom
        (Spec.map (CommRingCat.ofHom (algebraMap l.val K))) ∧
      ∀ i, LocallyOfFinitePresentation (Q i).hom ∧
        LocallyOfFinitePresentation (π i).left ∧ QuasiCompact (π i).left ∧
        IsSeparated (π i).left ∧
        IsPullback (mQ i) (partialFlagVariety G {s i}).toSpec (Q i).hom
          (Spec.map (CommRingCat.ofHom (algebraMap l.val K))) ∧
        IsPullback (partialFlagMorphism G {s i}).left mF (mQ i) (π i).left := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : ∀ i, IsAffineHom
      (pullback.diagonal (terminal.from (partialFlagVariety G {s i}).scheme)) :=
    fun i => variety_affine_diagonal (partialFlagVariety G {s i})
  choose R Q₀ b q₀ hR _hN hfp _hqc _hqs hQ using fun i =>
    exists_finite_arithmetic_scheme (partialFlagVariety G {s i}).toSpec
  obtain ⟨T, hstart, hT, hRT⟩ :=
    finite_coefficient_upper start.val start.property.1 R hR
  let k : CoefficientStage S := ⟨T, hT, start.property.2.trans hstart⟩
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap T K))
  let τ (i : I) := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hRT i)).toRingHom)
  let A : Over (Spec (.of T)) := stageScalarModel S F.hom k
  let B (i : I) : Over (Spec (.of T)) := Over.mk (pullback.fst (τ i) (b i))
  let X : Over (Spec (.of K)) := (flagVariety G).toOver
  let Y (i : I) : Over (Spec (.of K)) := (partialFlagVariety G {s i}).toOver
  obtain ⟨qA, _hAbase, hAorig, hAcart⟩ := source_scalar_square κ ρ
    (Spec.map (CommRingCat.ofHom (algebraMap S K))) X.hom F.hom qF
    (coefficient_triangle S T k.property.2) hF
  choose qB _hBbase _hBorig hBcart using fun i => source_scalar_square (τ i) ρ
    (Spec.map (CommRingCat.ofHom (algebraMap (R i) K)))
    (Y i).hom (b i) (q₀ i) (coefficient_triangle (R i) T (hRT i)) (hQ i)
  let : ∀ i, LocallyOfFinitePresentation (b i) := hfp
  let : LocallyOfFinitePresentation A.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst κ F.hom))
  let : QuasiCompact A.hom := inferInstanceAs (QuasiCompact (pullback.fst κ F.hom))
  let : IsSeparated A.hom := inferInstanceAs (IsSeparated (pullback.fst κ F.hom))
  let : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  let : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  let : ∀ i, LocallyOfFinitePresentation (B i).hom := fun i =>
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst (τ i) (b i)))
  let : ∀ _i : I, CompactSpace A.left := fun _ => inferInstance
  let : ∀ _i : I, QuasiSeparatedSpace A.left := fun _ => inferInstance
  obtain ⟨EF, hEF⟩ := cartesian_over_iso ρ X A qA hAcart
  choose EQ hEQ using fun i => cartesian_over_iso ρ (Y i) (B i) (qB i) (hBcart i)
  let g (i : I) : genericScalarModel T A.hom ⟶ genericScalarModel T (B i).hom :=
    EF.inv ≫ partialFlagMorphism G {s i} ≫ (EQ i).hom
  obtain ⟨l, _hl, π, hπ⟩ := exists_retained_maps T hT
    (fun _ : I => A.left) (fun i => (B i).left)
    (fun _ : I => A.hom) (fun i => (B i).hom) g ⟨T, hT, le_rfl⟩
  let Q (i : I) : Over (Spec (.of l.val)) := stageScalarModel T (B i).hom l
  let mF := scalar_stage_map T X A EF l
  let mQ (i : I) := scalar_stage_map T (Y i) (B i) (EQ i) l
  have hFcart : IsPullback mF X.hom (stageScalarModel T A.hom l).hom
      (Spec.map (CommRingCat.ofHom (algebraMap l.val K))) :=
    overIso_modelStage_cartesian T A.hom l X EF
  have hForig : mF ≫ pullback.snd _ A.hom ≫ pullback.snd _ F.hom = qF :=
    two_projections mF _ _ qA qF (retained_original T X A EF qA hEF l) hAorig
  let : Algebra.FiniteType ℤ l.val := (Subalgebra.fg_iff_finiteType l.val).mp l.property.1
  let : IsNoetherianRing l.val := Algebra.FiniteType.isNoetherianRing ℤ l.val
  let : LocallyOfFinitePresentation (stageScalarModel T A.hom l).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst _ A.hom))
  let : QuasiCompact (stageScalarModel T A.hom l).hom :=
    inferInstanceAs (QuasiCompact (pullback.fst _ A.hom))
  let : IsSeparated (stageScalarModel T A.hom l).hom :=
    inferInstanceAs (IsSeparated (pullback.fst _ A.hom))
  let : ∀ i, LocallyOfFinitePresentation (Q i).hom := fun i =>
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst _ (B i).hom))
  refine ⟨k, hstart, l, Q, π, mF, mQ, hForig, hFcart, ?_⟩
  intro i
  have hQcart : IsPullback (mQ i) (Y i).hom (Q i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap l.val K))) :=
    overIso_modelStage_cartesian T (B i).hom l (Y i) (EQ i)
  have hcomm : mF ≫ (π i).left = (partialFlagMorphism G {s i}).left ≫ mQ i :=
    retained_iso_square (Over.forget (Spec (.of K))) EF (EQ i)
      (partialFlagMorphism G {s i})
      ((modelScalarCone T A.hom).π.app (op l))
      ((modelScalarCone T (B i).hom).π.app (op l)) (π i).left (hπ i)
  have hprop := flag_arrow_properties (π i)
  exact ⟨inferInstance, hprop.1, hprop.2.1, hprop.2.2, hQcart,
    cartesian_arrow_square _ (partialFlagMorphism G {s i}) (π i) mF (mQ i)
      hFcart hQcart hcomm⟩

end SchubertGeometry
