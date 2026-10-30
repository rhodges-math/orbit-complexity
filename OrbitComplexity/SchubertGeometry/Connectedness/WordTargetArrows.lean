import OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointArrows
import OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Word endpoint maps to prescribed targets

Proper smooth word models and maps to specified target models can be
retained together. The target need not be an ordinary Schubert variety;
in particular the construction also applies to opposite endpoints.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u v

namespace SchubertGeometry

open private retain_endpoint_family proper_over_arrow
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointArrows
open private stage_map stage_map_cartesian stage_map_original
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected

private theorem projection_chain {C : Type*} [Category C]
    {A B D E : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (d : A ⟶ D) (e : A ⟶ E) (h : a ≫ b = d) (h' : d ≫ c = e) :
    a ≫ b ≫ c = e := by
  rw [← Category.assoc, h, h']

private theorem scalar_endpoint_properties {B T : Scheme.{u}}
    (κ : T ⟶ B) (A D : Over B)
    [IsProper A.hom] [Smooth A.hom] [IsSeparated D.hom]
    (f : Over.mk (pullback.fst κ A.hom) ⟶ Over.mk (pullback.fst κ D.hom)) :
    IsProper (pullback.fst κ A.hom) ∧ Smooth (pullback.fst κ A.hom) ∧
      IsProper f.left := by
  let : IsProper (Over.mk (pullback.fst κ A.hom)).hom := by
    change IsProper (pullback.fst κ A.hom)
    infer_instance
  let : IsSeparated (Over.mk (pullback.fst κ D.hom)).hom := by
    change IsSeparated (pullback.fst κ D.hom)
    infer_instance
  exact ⟨inferInstance, inferInstance, proper_over_arrow f⟩

/-- A finite family of word endpoints has proper smooth source models
and proper maps to scalar extensions of the prescribed targets, retaining
the Cartesian comparisons and their original projections. -/
theorem exists_word_target_arrows
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {I : Type v} [Finite I] (G : ReductiveGroupData K)
    (words : I → List G.rootBase.support)
    (Y : I → Over (Spec (.of K)))
    (fK : ∀ i, Over.mk (bsdhToSpec G (words i)) ⟶ Y i)
    (S : Subalgebra ℤ K) (hS : S.FG)
    (D : I → Over (Spec (.of S)))
    [∀ i, LocallyOfFinitePresentation (D i).hom] [∀ i, IsSeparated (D i).hom]
    (qD : ∀ i, (Y i).left ⟶ (D i).left)
    (hD : ∀ i, IsPullback (qD i) (Y i).hom (D i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k)
      (A : I → Over (Spec (.of k.val)))
      (l : CoefficientStage k.val)
      (f : ∀ i, stageScalarModel k.val (A i).hom l ⟶
        stageScalarModel k.val (stageScalarModel S (D i).hom k).hom l)
      (mA : ∀ i, bsdhScheme G (words i) ⟶
        (stageScalarModel k.val (A i).hom l).left)
      (mD : ∀ i, (Y i).left ⟶
        (stageScalarModel k.val (stageScalarModel S (D i).hom k).hom l).left),
      ∀ i,
        IsProper (stageScalarModel k.val (A i).hom l).hom ∧
        Smooth (stageScalarModel k.val (A i).hom l).hom ∧
        IsProper (f i).left ∧
        IsPullback (mA i) (bsdhToSpec G (words i))
          (stageScalarModel k.val (A i).hom l).hom
          (Spec.map (CommRingCat.ofHom (algebraMap l.val K))) ∧
        IsPullback (mD i) (Y i).hom
          (stageScalarModel k.val (stageScalarModel S (D i).hom k).hom l).hom
          (Spec.map (CommRingCat.ofHom (algebraMap l.val K))) ∧
        mD i ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom))
          (stageScalarModel S (D i).hom k).hom ≫
          pullback.snd
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
            (D i).hom = qD i ∧
        mA i ≫ (f i).left = (fK i).left ≫ mD i := by
  obtain ⟨k, hk, X, base, qA, hA⟩ :=
    exists_bsdh_family_models G words S hS start
  let : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
  let : IsScalarTower S k.val K :=
    Subalgebra.inclusion.isScalarTower_right k.property.2 K
  let A : I → Over (Spec (.of k.val)) := fun i => Over.mk (base i)
  let B : I → Over (Spec (.of k.val)) := fun i => stageScalarModel S (D i).hom k
  let (i : I) : IsProper (A i).hom := (hA i).1
  let (i : I) : Smooth (A i).hom := (hA i).2.1
  let (i : I) : CompactSpace (A i).left :=
    QuasiCompact.compactSpace_of_compactSpace (A i).hom
  let (i : I) : QuasiSeparatedSpace (A i).left :=
    quasiSeparatedSpace_of_quasiSeparated (A i).hom
  let (i : I) : LocallyOfFinitePresentation (B i).hom := by
    change LocallyOfFinitePresentation (pullback.fst _ (D i).hom)
    infer_instance
  let (i : I) : IsSeparated (B i).hom := by
    change IsSeparated (pullback.fst _ (D i).hom)
    infer_instance
  let qB : ∀ i, (Y i).left ⟶ (B i).left :=
    fun i => stage_map S (D i) (Y i) (qD i) (hD i) k
  have hB : ∀ i, IsPullback (qB i) (Y i).hom (B i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) :=
    fun i => stage_map_cartesian S (D i) (Y i) (qD i) (hD i) k
  obtain ⟨l, _hl, f, mA, mD, h⟩ :=
    retain_endpoint_family k.val k.property.1
      (fun i => Over.mk (bsdhToSpec G (words i))) Y A B fK qA qB
      (fun i => (hA i).2.2.2) hB ⟨k.val, k.property.1, le_rfl⟩
  refine ⟨k, hk, A, l, f, mA, mD, ?_⟩
  intro i
  obtain ⟨hcartA, hcartD, _hOldA, hOldD, hf, _hbase⟩ := h i
  have hproperties := scalar_endpoint_properties
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom))
    (A i) (B i) (f i)
  exact ⟨hproperties.1, hproperties.2.1, hproperties.2.2, hcartA, hcartD,
    projection_chain _ _ _ _ _ hOldD
      (stage_map_original S (D i) (Y i) (qD i) (hD i) k), hf⟩

end SchubertGeometry
