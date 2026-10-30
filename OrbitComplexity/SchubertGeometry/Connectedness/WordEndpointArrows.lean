import OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointModels
import OrbitComplexity.SchubertGeometry.BSDH.Factorization
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.RetainedMaps
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Arithmetic endpoint arrows for finite word families

The Bott–Samelson sources are chosen over one coefficient stage. Their specified
maps to the prescribed Schubert targets descend jointly to a further stage,
with Cartesian comparisons and the projections to the original targets.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting

namespace SchubertGeometry

universe u v

open private coefficient_triangle source_scalar_square
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointModels
open private scalarLeg_snd
  from OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent

private theorem cartesian_over_iso
    {B BK : Scheme.{u}} (ρ : BK ⟶ B) (X : Over BK) (Y : Over B)
    (q : X.left ⟶ Y.left) (h : IsPullback q X.hom Y.hom ρ) :
    ∃ E : X ≅ Over.mk (pullback.fst ρ Y.hom),
      E.hom.left ≫ pullback.snd ρ Y.hom = q := by
  refine ⟨Over.isoMk h.flip.isoPullback h.flip.isoPullback_hom_fst, ?_⟩
  exact h.flip.isoPullback_hom_snd

private theorem retained_iso_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y A B : C} {P Q : D} (e : X ≅ A) (d : Y ≅ B) (f : X ⟶ Y)
    (s : F.obj A ⟶ P) (t : F.obj B ⟶ Q) (z : P ⟶ Q)
    (h : s ≫ z = F.map (e.inv ≫ f ≫ d.hom) ≫ t) :
    (F.map e.hom ≫ s) ≫ z = F.map f ≫ (F.map d.hom ≫ t) := by
  calc
    (F.map e.hom ≫ s) ≫ z =
        F.map e.hom ≫ F.map (e.inv ≫ f ≫ d.hom) ≫ t := by
          rw [Category.assoc, h]
    _ = F.map (e.hom ≫ e.inv ≫ f ≫ d.hom) ≫ t := by
          simp only [Functor.map_comp, Category.assoc]
    _ = F.map f ≫ (F.map d.hom ≫ t) := by
          simp only [Iso.hom_inv_id_assoc, Functor.map_comp, Category.assoc]

private theorem precompose_projection {C : Type*} [Category C]
    {X Y Z W : C} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) {d : Y ⟶ W}
    (h : b ≫ c = d) : (a ≫ b) ≫ c = a ≫ d := by
  rw [Category.assoc, h]

private theorem retained_original
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (X : Over (Spec (.of K))) (Y : Over (Spec (.of S)))
    (E : X ≅ genericScalarModel S Y.hom) (q : X.left ⟶ Y.left)
    (h : E.hom.left ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) Y.hom = q)
    (k : CoefficientStage S) :
    (E.hom.left ≫ (modelScalarCone S Y.hom).π.app (op k)) ≫
      pullback.snd _ Y.hom = q := by
  exact (precompose_projection (C := Scheme) E.hom.left
    ((modelScalarCone S Y.hom).π.app (op k)) _
    (scalarLeg_snd S Y.hom k)).trans h

private theorem proper_over_arrow
    {B : Scheme.{u}} {X Y : Over B} [IsProper X.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) : IsProper f.left := by
  have : IsProper (f.left ≫ Y.hom) := by
    rw [f.w]
    infer_instance
  exact IsProper.of_comp f.left Y.hom

private theorem retain_endpoint_family
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} [Finite I]
    (X Y : I → Over (Spec (.of K))) (A B : I → Over (Spec (.of S)))
    [∀ i, CompactSpace (A i).left] [∀ i, QuasiSeparatedSpace (A i).left]
    [∀ i, LocallyOfFinitePresentation (B i).hom]
    (f : ∀ i, X i ⟶ Y i)
    (qA : ∀ i, (X i).left ⟶ (A i).left)
    (qB : ∀ i, (Y i).left ⟶ (B i).left)
    (hA : ∀ i, IsPullback (qA i) (X i).hom (A i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hB : ∀ i, IsPullback (qB i) (Y i).hom (B i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k)
      (f₀ : ∀ i, stageScalarModel S (A i).hom k ⟶ stageScalarModel S (B i).hom k)
      (mX : ∀ i, (X i).left ⟶ (stageScalarModel S (A i).hom k).left)
      (mY : ∀ i, (Y i).left ⟶ (stageScalarModel S (B i).hom k).left),
      ∀ i,
        IsPullback (mX i) (X i).hom (stageScalarModel S (A i).hom k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
        IsPullback (mY i) (Y i).hom (stageScalarModel S (B i).hom k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
        mX i ≫ pullback.snd _ (A i).hom = qA i ∧
        mY i ≫ pullback.snd _ (B i).hom = qB i ∧
        mX i ≫ (f₀ i).left = (f i).left ≫ mY i ∧
        (f₀ i).left ≫ (stageScalarModel S (B i).hom k).hom =
          (stageScalarModel S (A i).hom k).hom := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  choose EA hEA using fun i => cartesian_over_iso ρ (X i) (A i) (qA i) (hA i)
  choose EB hEB using fun i => cartesian_over_iso ρ (Y i) (B i) (qB i) (hB i)
  let g (i : I) : genericScalarModel S (A i).hom ⟶ genericScalarModel S (B i).hom :=
    (EA i).inv ≫ f i ≫ (EB i).hom
  obtain ⟨k, hstart, f₀, hf⟩ := exists_retained_maps S hS
    (fun i => (A i).left) (fun i => (B i).left)
    (fun i => (A i).hom) (fun i => (B i).hom) g start
  let mX (i : I) := (EA i).hom.left ≫ (modelScalarCone S (A i).hom).π.app (op k)
  let mY (i : I) := (EB i).hom.left ≫ (modelScalarCone S (B i).hom).π.app (op k)
  refine ⟨k, hstart, f₀, mX, mY, ?_⟩
  intro i
  refine ⟨overIso_modelStage_cartesian S (A i).hom k (X i) (EA i),
    overIso_modelStage_cartesian S (B i).hom k (Y i) (EB i),
    retained_original S (X i) (A i) (EA i) (qA i) (hEA i) k,
    retained_original S (Y i) (B i) (EB i) (qB i) (hEB i) k, ?_, (f₀ i).w⟩
  exact retained_iso_square (Over.forget (Spec (.of K))) (EA i) (EB i) (f i)
    ((modelScalarCone S (A i).hom).π.app (op k))
    ((modelScalarCone S (B i).hom).π.app (op k)) (f₀ i).left (hf i)

private theorem two_projections
    {C : Type*} [Category C] {X Y Z W : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (d : X ⟶ Z) (e : X ⟶ W)
    (h : a ≫ b = d) (h' : d ≫ c = e) : a ≫ b ≫ c = e := by
  rw [← Category.assoc, h, h']

/-- The specified endpoints of finitely many reduced words descend jointly from
newly constructed Bott–Samelson sources to the prescribed Schubert target
models. Cartesian comparisons, structure equations and projections to the
original targets are retained. -/
theorem exists_word_endpoint_arrows
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {I : Type v} [Finite I] (G : ReductiveGroupData K)
    (words : I → List G.rootBase.support)
    (hred : ∀ i, (weylCoxeterSystem G.rootBase).IsReduced (words i))
    (S : Subalgebra ℤ K) (hS : S.FG) (start : CoefficientStage S)
    (D : I → Over (Spec (.of S)))
    [∀ i, LocallyOfFinitePresentation (D i).hom] [∀ i, IsSeparated (D i).hom]
    (qD : ∀ i, (schubertVariety G (simpleWeylWord G.rootBase (words i))).scheme ⟶ (D i).left)
    (hD : ∀ i, IsPullback (qD i)
      (schubertVariety G (simpleWeylWord G.rootBase (words i))).toSpec (D i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k)
      (A : I → Over (Spec (.of k.val)))
      (qA : ∀ i, bsdhScheme G (words i) ⟶ (A i).left)
      (l : CoefficientStage k.val)
      (f : ∀ i, stageScalarModel k.val (A i).hom l ⟶
        stageScalarModel k.val (stageScalarModel S (D i).hom k).hom l)
      (mA : ∀ i, bsdhScheme G (words i) ⟶
        (stageScalarModel k.val (A i).hom l).left)
      (mD : ∀ i, (schubertVariety G (simpleWeylWord G.rootBase (words i))).scheme ⟶
        (stageScalarModel k.val (stageScalarModel S (D i).hom k).hom l).left),
      ∀ i, IsProper (A i).hom ∧ Smooth (A i).hom ∧
        GeometricallyConnected (A i).hom ∧
        IsPullback (qA i) (bsdhToSpec G (words i)) (A i).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
        IsPullback (mA i) (bsdhToSpec G (words i))
          (stageScalarModel k.val (A i).hom l).hom
          (Spec.map (CommRingCat.ofHom (algebraMap l.val K))) ∧
        IsPullback (mD i)
          (schubertVariety G (simpleWeylWord G.rootBase (words i))).toSpec
          (stageScalarModel k.val (stageScalarModel S (D i).hom k).hom l).hom
          (Spec.map (CommRingCat.ofHom (algebraMap l.val K))) ∧
        mA i ≫ pullback.snd _ (A i).hom = qA i ∧
        mD i ≫ pullback.snd _ (stageScalarModel S (D i).hom k).hom ≫
          pullback.snd _ (D i).hom = qD i ∧
        mA i ≫ (f i).left = (bsdhSchubertMap G (words i) (hred i)).left ≫ mD i ∧
        (f i).left ≫ (stageScalarModel k.val
          (stageScalarModel S (D i).hom k).hom l).hom =
            (stageScalarModel k.val (A i).hom l).hom ∧
        IsProper (f i).left := by
  classical
  obtain ⟨k, hstart, Y₀, a, qA, hA⟩ := exists_bsdh_family_models G words S hS start
  let A (i : I) : Over (Spec (.of k.val)) := Over.mk (a i)
  let B (i : I) : Over (Spec (.of k.val)) := stageScalarModel S (D i).hom k
  let X (i : I) : Over (Spec (.of K)) := (bsdhVariety G (words i)).toOver
  let Z (i : I) : Over (Spec (.of K)) :=
    (schubertVariety G (simpleWeylWord G.rootBase (words i))).toOver
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k.val K))
  choose qB _hBbase hBorig hBcart using fun i =>
    source_scalar_square κ ρ
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))
      (Z i).hom (D i).hom (qD i)
      (coefficient_triangle S k.val k.property.2) (hD i)
  let : ∀ i, IsProper (A i).hom := fun i => (hA i).1
  let : ∀ i, CompactSpace (A i).left := fun i =>
    QuasiCompact.compactSpace_of_compactSpace (A i).hom
  let : ∀ i, QuasiSeparatedSpace (A i).left := fun i =>
    quasiSeparatedSpace_of_quasiSeparated (A i).hom
  let : ∀ i, LocallyOfFinitePresentation (B i).hom := fun i =>
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst κ (D i).hom))
  let fK (i : I) : X i ⟶ Z i := bsdhSchubertMap G (words i) (hred i)
  obtain ⟨l, _hl, f, mA, mB, hf⟩ := retain_endpoint_family k.val k.property.1
    X Z A B fK qA qB (fun i => (hA i).2.2.2) hBcart
    ⟨k.val, k.property.1, le_rfl⟩
  refine ⟨k, hstart, A, qA, l, f, mA, mB, ?_⟩
  intro i
  have hproj : mB i ≫ pullback.snd _ (stageScalarModel S (D i).hom k).hom ≫
      pullback.snd _ (D i).hom = qD i :=
    two_projections (mB i) _ _ (qB i) (qD i) (hf i).2.2.2.1 (hBorig i)
  have : IsProper (stageScalarModel k.val (A i).hom l).hom :=
    inferInstanceAs (IsProper (pullback.fst _ (A i).hom))
  have : IsSeparated (B i).hom :=
    inferInstanceAs (IsSeparated (pullback.fst κ (D i).hom))
  have : IsSeparated (stageScalarModel k.val (B i).hom l).hom :=
    inferInstanceAs (IsSeparated (pullback.fst _ (B i).hom))
  exact ⟨(hA i).1, (hA i).2.1, (hA i).2.2.1, (hA i).2.2.2,
    (hf i).1, (hf i).2.1, (hf i).2.2.1, hproj,
    (hf i).2.2.2.2.1, (hf i).2.2.2.2.2, proper_over_arrow (f i)⟩

end SchubertGeometry
