import OrbitComplexity.SchubertGeometry.Normality.Components.OppositeTargetStages
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Prime ideals of prescribed opposite Schubert models -/

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups FrobeniusSplitting

namespace SchubertGeometry

universe u

open private noetherian_fibre from
  OrbitComplexity.SchubertGeometry.Normality.Components.OppositePrimeStages

private theorem factor_scalar_square
    {B T V : Scheme.{u}} (s : T ⟶ B) (τ : V ⟶ T)
    (D : Over B) (Y : Over V) (qY : Y.left ⟶ D.left)
    (a : V ⟶ B) (ha : a = τ ≫ s)
    (hY : IsPullback qY Y.hom D.hom a) :
    ∃ qT : Y.left ⟶ (pullback s D.hom : Scheme.{u}),
      IsPullback qT Y.hom (pullback.fst s D.hom) τ ∧
      qT ≫ pullback.snd s D.hom = qY := by
  have hY' : IsPullback qY Y.hom D.hom (τ ≫ s) := ha ▸ hY
  have w : (Y.hom ≫ τ) ≫ s = qY ≫ D.hom :=
    (Category.assoc Y.hom τ s).trans hY'.w.symm
  refine ⟨pullback.lift (Y.hom ≫ τ) qY w, ?_, pullback.lift_snd _ _ _⟩
  have hOuter : IsPullback
      (pullback.lift (Y.hom ≫ τ) qY w ≫ pullback.snd s D.hom)
      Y.hom D.hom (τ ≫ s) := by
    simpa only [pullback.lift_snd] using hY'
  exact hOuter.of_right (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback s D.hom).flip

private theorem scalar_arrow_to_model
    {B V : Scheme.{u}} (τ : V ⟶ B)
    (C D : Over B) (e : C ⟶ D) (Y : Over V)
    (qY : Y.left ⟶ D.left) (hY : IsPullback qY Y.hom D.hom τ) :
    ∃ f : Over.mk (pullback.fst τ C.hom) ⟶ Y,
      f.left ≫ qY = pullback.snd τ C.hom ≫ e.left := by
  have w : (pullback.snd τ C.hom ≫ e.left) ≫ D.hom =
      pullback.fst τ C.hom ≫ τ := by
    calc
      (pullback.snd τ C.hom ≫ e.left) ≫ D.hom =
          pullback.snd τ C.hom ≫ (e.left ≫ D.hom) := Category.assoc _ _ _
      _ = pullback.snd τ C.hom ≫ C.hom :=
        congrArg (fun g => pullback.snd τ C.hom ≫ g) e.w
      _ = pullback.fst τ C.hom ≫ τ :=
        (pullback.condition (f := τ) (g := C.hom)).symm
  refine ⟨Over.homMk (hY.lift (pullback.snd τ C.hom ≫ e.left)
    (pullback.fst τ C.hom) w) (hY.lift_snd _ _ _), ?_⟩
  exact hY.lift_fst _ _ _

private theorem inclusion_scalar_spec
    {K : Type u} [CommRing K] {S T R : Subalgebra ℤ K}
    (hST : S ≤ T) (hTR : T ≤ R) {L : Type u} [CommRing L] (a : R →+* L) :
    Spec.map (CommRingCat.ofHom
      (a.comp (Subalgebra.inclusion (hST.trans hTR)).toRingHom)) =
      Spec.map (CommRingCat.ofHom (a.comp (Subalgebra.inclusion hTR).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1

/-- On one coefficient stage, the field fibres of an opposite Schubert model are
integral and all their affine image ideals are prime or the unit ideal. -/
theorem exists_opposite_closed_primes {K : Type u} [hK : Field K]
    [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (S : Subalgebra ℤ K) (hS : S.FG) (D : Over (Spec (.of S)))
    [hDFP : LocallyOfFinitePresentation D.hom] [hDCompact : CompactSpace D.left]
    (qD : (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toOver.left ⟶ D.left)
    (hD : IsPullback qD (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toOver.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ start ≤ R ∧ ∃ hSR : S ≤ R,
      ∀ (L : Type u) [Field L] [Algebra R L]
        (YL : Over (Spec (.of L))) (qYL : YL.left ⟶ D.left)
        (_hYL : IsPullback qYL YL.hom D.hom
          (Spec.map (CommRingCat.ofHom
            ((algebraMap R L).comp (Subalgebra.inclusion hSR).toRingHom)))),
        IsIntegral YL.left ∧
          ∀ (Z : Scheme.{u}) (j : YL.left ⟶ Z) (U : Z.affineOpens),
            j.ker.ideal U = ⊤ ∨ (j.ker.ideal U).IsPrime := by
  have target := @exists_opposite_target_stage K hK hAlg hChar G word hred
    S hS D hDFP qD hD start hstart
  obtain ⟨T, hT, hST, hstartT, C, e, qC, qDt, hCProper, hCSmooth,
    hC, hDt, htriangle⟩ := target
  have hSFinite : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
  have hTFinite : Algebra.FiniteType ℤ T := (Subalgebra.fg_iff_finiteType T).mp hT
  have hDprops := @finiteType_int_scheme_properties S (inferInstance : CommRing S)
    hSFinite D.left hDCompact D.hom hDFP
  have hDQC : QuasiCompact D.hom := hDprops.2.1
  have hDTCompact : CompactSpace (stageScalarModel S D.hom ⟨T, hT, hST⟩).left := by
    change CompactSpace (pullback
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom)) D.hom :
      Scheme.{u})
    infer_instance
  have hDTFP : LocallyOfFinitePresentation
      (stageScalarModel S D.hom ⟨T, hT, hST⟩).hom := by
    change LocallyOfFinitePresentation (pullback.fst
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom)) D.hom)
    infer_instance
  have hCCompact : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
  have hCFP : LocallyOfFinitePresentation C.hom := inferInstance
  have hCLFT : LocallyOfFiniteType C.hom := inferInstance
  have hCprops := @finiteType_int_scheme_properties T (inferInstance : CommRing T)
    hTFinite C.left hCCompact C.hom hCFP
  have hCNoeth : IsNoetherian C.left := hCprops.1
  have hEQC : QuasiCompact e.left := inferInstance
  have primes := @exists_opposite_prime_stage K hK hAlg hChar G word hred
    T hT C (stageScalarModel S D.hom ⟨T, hT, hST⟩) hCFP hDTFP
    hCCompact hDTCompact e hEQC qC qDt hC hDt htriangle T hT
  obtain ⟨R, hR, _hstartR, hTR, hfields⟩ := primes
  refine ⟨R, hR, hstartT.trans hTR, hST.trans hTR, ?_⟩
  intro L hL hRL YL qYL hYL
  have intermediate := @factor_scalar_square (Spec (.of S)) (Spec (.of T))
    (Spec (.of L))
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom))
    (Spec.map (CommRingCat.ofHom
      ((algebraMap R L).comp (Subalgebra.inclusion hTR).toRingHom)))
    D YL qYL
    (Spec.map (CommRingCat.ofHom
      ((algebraMap R L).comp (Subalgebra.inclusion (hST.trans hTR)).toRingHom)))
    (@inclusion_scalar_spec K hK.toCommRing S T R hST hTR L hL.toCommRing
      (algebraMap R L)) hYL
  obtain ⟨qYT, hYT, _hOriginal⟩ := intermediate
  have arrow := @scalar_arrow_to_model (Spec (.of T)) (Spec (.of L))
    (Spec.map (CommRingCat.ofHom
      ((algebraMap R L).comp (Subalgebra.inclusion hTR).toRingHom)))
    C (stageScalarModel S D.hom ⟨T, hT, hST⟩) e YL qYT hYT
  obtain ⟨fL, hfL⟩ := arrow
  have hXLNoeth := @noetherian_fibre (Spec (.of T)) L hL C hCprops.2.1 hCLFT
    (Spec.map (CommRingCat.ofHom
      ((algebraMap R L).comp (Subalgebra.inclusion hTR).toRingHom)))
    (Over.mk (pullback.fst (Spec.map (CommRingCat.ofHom
      ((algebraMap R L).comp (Subalgebra.inclusion hTR).toRingHom))) C.hom))
    (pullback.snd (Spec.map (CommRingCat.ofHom
      ((algebraMap R L).comp (Subalgebra.inclusion hTR).toRingHom))) C.hom)
    (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom
      ((algebraMap R L).comp (Subalgebra.inclusion hTR).toRingHom))) C.hom).flip
  have hFQC : QuasiCompact fL.left := inferInstance
  exact @hfields L hL hRL
    (Over.mk (pullback.fst (Spec.map (CommRingCat.ofHom
      ((algebraMap R L).comp (Subalgebra.inclusion hTR).toRingHom))) C.hom))
    YL fL hFQC
    (pullback.snd (Spec.map (CommRingCat.ofHom
      ((algebraMap R L).comp (Subalgebra.inclusion hTR).toRingHom))) C.hom)
    qYT
    (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom
      ((algebraMap R L).comp (Subalgebra.inclusion hTR).toRingHom))) C.hom).flip
    hYT hfL

end SchubertGeometry
