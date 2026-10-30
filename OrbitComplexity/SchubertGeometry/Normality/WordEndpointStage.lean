import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInduction
import OrbitComplexity.SchubertGeometry.Normality.WordFaceImageStages
import OrbitComplexity.SchubertGeometry.Connectedness.ChosenPairedRetention
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.BirationalSchemeStages
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.Perfect
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Endpoint morphisms and field splittings for word models

The word endpoint descends between the scalar extensions of its coefficient
models. A normalized prefix functional then supplies compatible splittings
on field fibres at every possible prime characteristic.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits FrobeniusSplitting
open ReductiveGroups FrobeniusSplitting.RetainedCharacter

open private modelComparison modelComparison_projection from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares
open private scalarLeg_snd from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent
open private transportOverMap transportOverMap_comparison
  over_source_cartesian genericStage_cartesian from
  OrbitComplexity.SchubertGeometry.Normality.WordFaceImageStages

open private endpoint_from_projections from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.BirationalSchemeStages

open private singletonIndex from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames

namespace SchubertGeometry

private theorem composite_projection {D : Type u} [Category.{v} D]
    {A B C E : D} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E)
    (q : B ⟶ E) (m : A ⟶ E) (hb : b ≫ c = q) (ha : a ≫ q = m) :
    (a ≫ b) ≫ c = m := by
  rw [Category.assoc, hb]
  exact ha

/-- The endpoint of the carried word model descends after a coefficient
extension, preserving its original word and flag comparisons. -/
theorem exists_prefix_endpoint_stage {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List G.rootBase.support}
    (S : Subalgebra ℤ K) (hS : S.FG) (C F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [LocallyOfFinitePresentation F.hom]
    (qC : bsdhScheme G word ⟶ C.left)
    (hC : IsPullback qC (bsdhToSpec G word) C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t)
      (endpoint : stageScalarModel S C.hom t ⟶ stageScalarModel S F.hom t)
      (m : bsdhScheme G word ⟶ (stageScalarModel S C.hom t).left)
      (q : (flagVariety G).scheme ⟶ (stageScalarModel S F.hom t).left),
      IsPullback m (bsdhToSpec G word) (stageScalarModel S C.hom t).hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
      IsPullback q (flagVariety G).toSpec (stageScalarModel S F.hom t).hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
      m ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
        C.hom = qC ∧
      q ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
        F.hom = qF ∧
      bsdhMap G word ≫ q = m ≫ endpoint.left := by
  let source : Over (Spec (.of K)) := Over.mk (bsdhToSpec G word)
  let native : source ⟶ (flagVariety G).toOver := Over.homMk (bsdhMap G word) rfl
  let α : source ≅ genericScalarModel S C.hom :=
    @modelComparison.{u} (Spec (.of S)) (Spec (.of K)) (Spec.map (CommRingCat.ofHom (algebraMap S
      K))) C source qC hC
  let β : (flagVariety G).toOver ≅ genericScalarModel S F.hom :=
    @modelComparison.{u} (Spec (.of S)) (Spec (.of K)) (Spec.map (CommRingCat.ofHom (algebraMap S
      K))) F (flagVariety G).toOver qF hF
  obtain ⟨r, er, her⟩ := @exists_model_morphism.{u} K (@Field.toCommRing K kField)
    S hS C.left F.left inferInstance inferInstance C.hom F.hom
    inferInstance (transportOverMap α β native)
  obtain ⟨t, hrt, hstart⟩ := exists_ge_ge r start
  let et := extendModelMorphism S C.hom F.hom hrt er
  have het := extendModelMorphism_baseChange S C.hom F.hom hrt er
    (transportOverMap α β native) her
  refine ⟨t, hstart, et,
    α.hom.left ≫ (modelScalarCone S C.hom).π.app (Opposite.op t),
    β.hom.left ≫ (modelScalarCone S F.hom).π.app (Opposite.op t), ?_, ?_, ?_, ?_, ?_⟩
  · exact over_source_cartesian α _ _ _ (genericStage_cartesian S C t)
  · exact over_source_cartesian β _ _ _ (genericStage_cartesian S F t)
  ·
    exact composite_projection α.hom.left
      ((modelScalarCone S C.hom).π.app (Opposite.op t))
      (pullback.snd _ C.hom) (pullback.snd _ C.hom) qC
      (scalarLeg_snd S C.hom t) (@modelComparison_projection.{u} (Spec (.of S)) (Spec (.of K))
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) C source qC hC)
  ·
    exact composite_projection β.hom.left
      ((modelScalarCone S F.hom).π.app (Opposite.op t))
      (pullback.snd _ F.hom) (pullback.snd _ F.hom) qF
      (scalarLeg_snd S F.hom t) (@modelComparison_projection.{u} (Spec (.of S)) (Spec (.of K))
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) F (flagVariety G).toOver qF hF)
  ·
    exact (transportOverMap_comparison α β native _ _ et.left het).symm

namespace RetainedCharacter
open ReductiveGroups
private theorem prime_fibre_compatible {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : PrefixModel G word) (hM : PrefixSplits M)
    (κ : Type u) [κField : Field κ] (p : ℕ) [hpPrime : Fact p.Prime] [CharP κ p]
    (coefficientMap : Spec (.of κ) ⟶ Spec (.of M.S))
    (X : Scheme.{u}) (baseκ : X ⟶ Spec (.of κ)) (x : X ⟶ M.cG.pt.left)
    (hx : IsPullback x baseκ M.cG.pt.hom coefficientMap)
    (B : Fin word.length → Over X)
    (bD : ∀ j, (B j).left ⟶ (M.boundaries j).left)
    (hB : ∀ j, IsPullback (B j).hom (bD j) x (M.boundaries j).hom) :
    let L := (Scheme.Modules.pullback x).obj
      (@matchingModule.{u} M.S M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K
        kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S)
        M.N M.cG M.delta ((p - 1) / 2))
    let m := @pullSection.{u} X M.cG.pt.left x
      (@matchingModule.{u} M.S M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K
        kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S)
        M.N M.cG M.delta ((p - 1) / 2))
      (@coefficientMatchingSection.{u} M.S M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) M.S)
        M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr
        ((p - 1) / 2))
    ∃ cκAlg : Algebra (ULift.{u} (ZMod p)) κ,
      ∃ data : @SectionSplitting.{u} (ULift.{u} (ZMod p))
          (@Field.toCommRing (ULift.{u} (ZMod p))
            (inferInstanceAs (Field (ULift.{u} (ZMod p))))) p
          (inferInstanceAs (ExpChar (ULift.{u} (ZMod p)) p)) X
          (baseκ ≫ Spec.map (CommRingCat.ofHom
            (@algebraMap (ULift.{u} (ZMod p)) κ _ _ cκAlg))) L
          (m.app ⊤ (1 : Γ(X, ⊤))),
        ∀ j, data.sigma.IsCompatible (B j).hom.ker := by
  intro L m
  have hp : p.Prime := hpPrime.out
  have hOdd : Odd p := by
    apply hp.odd_of_ne_two
    intro hp2
    have hne : (2 : κ) ≠ 0 := by
      simpa only [map_ofNat] using
        (M.twoUnit.map (Spec.preimage coefficientMap).hom).ne_zero
    apply hne
    subst p
    exact CharP.cast_eq_zero κ 2
  let zκAlg : Algebra (ZMod p) κ := ZMod.algebra κ p
  let cκAlg : Algebra (ULift.{u} (ZMod p)) κ :=
    @ULift.algebra' (ZMod p) κ
      (inferInstanceAs (CommSemiring (ZMod p)))
      (inferInstanceAs (Semiring κ)) zκAlg
  refine ⟨cκAlg, ?_⟩
  exact @PrefixModel.fibre_splitting.{u} K kField kClosed kZero G word M hM
    κ (@Field.toCommRing κ κField) (Field.toIsField κ)
    (ULift.{u} (ZMod p)) (inferInstanceAs (Field (ULift.{u} (ZMod p)))) cκAlg
    p (inferInstanceAs (ExpChar (ULift.{u} (ZMod p)) p))
    (inferInstanceAs (PerfectRing (ULift.{u} (ZMod p)) p)) hOdd hp.one_lt
    coefficientMap X baseκ x hx B bD hB
end RetainedCharacter



private theorem boundary_scalar_cartesian {A B X Y Z : Scheme.{u}}
    (d : A ⟶ B) (n : A ⟶ Z) (m : B ⟶ Y) (z : Z ⟶ Y)
    (h : IsPullback d n m z) (q : X ⟶ Y) (m' : B ⟶ X)
    (hm : m' ≫ q = m) :
    ∃ n' : A ⟶ pullback q z, IsPullback d n' m' (pullback.fst q z) := by
  have hOuter : IsPullback d n (m' ≫ q) z := by
    rw [hm]
    exact h
  exact ⟨_, IsPullback.of_bot' hOuter (IsPullback.of_hasPullback q z)⟩


private theorem scalar_schubert_boundaries {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List G.rootBase.support}
    (M : RetainedCharacter.PrefixModel G word)
    (S : Subalgebra ℤ K) (C F : Over (Spec (.of S)))
    (qOriginal : C.left ⟶ M.cG.pt.left)
    (D : G.weylGroup → Over (Spec (.of S)))
    (j : ∀ x, D x ⟶ F)
    (qD : ∀ x, (schubertVariety G x).toOver.left ⟶ (D x).left)
    (hD : ∀ x, IsPullback (qD x) (schubertVariety G x).toOver.hom (D x).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hj : ∀ x, (schubertInclusion G x).left ≫ qF = qD x ≫ (j x).left)
    (t : CoefficientStage S)
    (m : bsdhScheme G word ⟶ (stageScalarModel S C.hom t).left)
    (q : (flagVariety G).scheme ⟶ (stageScalarModel S F.hom t).left)
    (hq : IsPullback q (flagVariety G).toSpec (stageScalarModel S F.hom t).hom
      (Spec.map (CommRingCat.ofHom (algebraMap t.val K))))
    (hmProjection : m ≫ (pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
      C.hom ≫ qOriginal) = M.m₀)
    (hqProjection : q ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
      F.hom = qF) :
    let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
    let DT := fun x => stageScalarModel S (D x).hom t
    let jT := fun x => chosenScalarArrow τ (j x)
    let qMT := pullback.snd τ C.hom ≫ qOriginal
    let boundaries := fun k => Over.mk (pullback.fst qMT (M.boundaries k).hom)
    ∃ (qDT : ∀ x, (schubertVariety G x).toOver.left ⟶ (DT x).left),
      (∀ x, IsPullback (qDT x) (schubertVariety G x).toOver.hom (DT x).hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K)))) ∧
      (∀ x, (schubertInclusion G x).left ≫ q = qDT x ≫ (jT x).left) ∧
      (∀ k, IsClosedImmersion (boundaries k).hom) ∧
      ∃ (n : ∀ k, bsdhScheme G (word.eraseIdx k.val) ⟶ (boundaries k).left),
        ∀ k, IsPullback (bsdhOmitMap G word k) (n k) m (boundaries k).hom := by
  classical
  intro τ DT jT qMT boundaries
  let αD := fun x => @modelComparison.{u} (Spec (.of S)) (Spec (.of K))
    (Spec.map (CommRingCat.ofHom (algebraMap S K))) (D x)
    (schubertVariety G x).toOver (qD x) (hD x)
  let qDT := fun x => (αD x).hom.left ≫
    (modelScalarCone S (D x).hom).π.app (Opposite.op t)
  have hDT (x) : IsPullback (qDT x) (schubertVariety G x).toOver.hom (DT x).hom
      (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) :=
    over_source_cartesian (αD x) _ _ _ (genericStage_cartesian S (D x) t)
  have hDTProjection (x) : qDT x ≫ pullback.snd τ (D x).hom = qD x :=
    composite_projection (αD x).hom.left ((modelScalarCone S (D x).hom).π.app (Opposite.op t))
      (pullback.snd τ (D x).hom) (pullback.snd _ (D x).hom) (qD x)
      (scalarLeg_snd S (D x).hom t)
      (@modelComparison_projection.{u} (Spec (.of S)) (Spec (.of K))
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) (D x)
        (schubertVariety G x).toOver (qD x) (hD x))
  have hjT (x) : (schubertInclusion G x).left ≫ q = qDT x ≫ (jT x).left :=
    @endpoint_from_projections.{u} (Spec (.of S)) (Spec (.of t.val)) (Spec (.of K))
      τ (Spec.map (CommRingCat.ofHom (algebraMap t.val K)))
      (D x) F (DT x) (stageScalarModel S F.hom t) (schubertVariety G x).toOver (flagVariety
        G).toOver
      (pullback.snd τ (D x).hom) (pullback.snd τ F.hom)
      (IsPullback.of_hasPullback τ F.hom).flip
      (j x) (jT x) (chosenScalarArrow_snd τ (j x))
      (qD x) qF (qDT x) q (hDTProjection x) hqProjection
      (hDT x).w hq.w (schubertInclusion G x) (hj x)
  have hBoundaryClosed (k) : IsClosedImmersion (boundaries k).hom := by
    let : IsClosedImmersion (M.boundaries k).hom := M.hclosed k
    change IsClosedImmersion (pullback.fst qMT (M.boundaries k).hom)
    infer_instance
  choose n hn using fun (k : Fin word.length) => @boundary_scalar_cartesian.{u}
    (bsdhScheme G (word.eraseIdx k.val)) (bsdhScheme G word) (stageScalarModel S C.hom t).left
      M.cG.pt.left
    (M.boundaries k).left (bsdhOmitMap G word k) (M.nB k) M.m₀ (M.boundaries k).hom
    (M.hnB k) qMT m hmProjection
  exact ⟨qDT, hDT, hjT, hBoundaryClosed, n, hn⟩


end SchubertGeometry
