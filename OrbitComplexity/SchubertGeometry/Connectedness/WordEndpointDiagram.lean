import OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointArrows
import OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointTriangles
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # A common flag comparison for a finite endpoint family

The source and endpoint construction is combined with the given closed
Schubert inclusions. One flag comparison is shared by the whole family after
the same two coefficient extensions. Its projections retain the original
flag model, and the target comparisons retain the given Schubert models.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u v

namespace SchubertGeometry

open private coefficient_triangle source_scalar_square
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointModels
open private scalar_triangle scalarArrow_isPullback
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointTriangles

private theorem inner_projection_base {T U X : Scheme.{u}}
    (τ : U ⟶ T) (ρ : X ⟶ U) {Y : Scheme.{u}} (a : Y ⟶ T)
    {Z : Scheme.{u}} (z : Z ⟶ X) (q : Z ⟶ pullback τ a)
    (hf : q ≫ pullback.fst τ a = z ≫ ρ) :
    (q ≫ pullback.snd τ a) ≫ a = z ≫ (ρ ≫ τ) := by
  calc
    (q ≫ pullback.snd τ a) ≫ a = q ≫ (pullback.snd τ a ≫ a) :=
      Category.assoc _ _ _
    _ = q ≫ (pullback.fst τ a ≫ τ) :=
      congrArg (fun f => q ≫ f) (pullback.condition (f := τ) (g := a)).symm
    _ = (q ≫ pullback.fst τ a) ≫ τ := (Category.assoc _ _ _).symm
    _ = (z ≫ ρ) ≫ τ := congrArg (fun f => f ≫ τ) hf
    _ = z ≫ (ρ ≫ τ) := Category.assoc _ _ _

private theorem nested_scalar_triangle {B T U BK : Scheme.{u}}
    (κ : T ⟶ B) (τ : U ⟶ T) (ρ : BK ⟶ U)
    {C D : Over B} {CK DK : Over BK} (e : C ⟶ D) (eK : CK ⟶ DK)
    (qC : CK.left ⟶ C.left) (qD : DK.left ⟶ D.left)
    (he : qC ≫ e.left = eK.left ≫ qD)
    (qCT : CK.left ⟶ pullback τ (pullback.fst κ C.hom))
    (qDT : DK.left ⟶ pullback τ (pullback.fst κ D.hom))
    (hCf : qCT ≫ pullback.fst τ (pullback.fst κ C.hom) = CK.hom ≫ ρ)
    (hDf : qDT ≫ pullback.fst τ (pullback.fst κ D.hom) = DK.hom ≫ ρ)
    (hCs : (qCT ≫ pullback.snd τ (pullback.fst κ C.hom)) ≫
      pullback.snd κ C.hom = qC)
    (hDs : (qDT ≫ pullback.snd τ (pullback.fst κ D.hom)) ≫
      pullback.snd κ D.hom = qD) :
    qCT ≫ (chosenScalarArrow τ (chosenScalarArrow κ e)).left = eK.left ≫ qDT := by
  let C₁ : Over T := Over.mk (pullback.fst κ C.hom)
  let D₁ : Over T := Over.mk (pullback.fst κ D.hom)
  let qC₁ := qCT ≫ pullback.snd τ C₁.hom
  let qD₁ := qDT ≫ pullback.snd τ D₁.hom
  have hC₁ : qC₁ ≫ C₁.hom = CK.hom ≫ (ρ ≫ τ) :=
    inner_projection_base τ ρ C₁.hom CK.hom qCT hCf
  have hD₁ : qD₁ ≫ D₁.hom = DK.hom ≫ (ρ ≫ τ) :=
    inner_projection_base τ ρ D₁.hom DK.hom qDT hDf
  have hfirst := scalar_triangle κ (ρ ≫ τ) e eK qC qD he qC₁ qD₁
    hC₁ hCs hD₁ hDs
  exact scalar_triangle τ ρ (chosenScalarArrow κ e) eK qC₁ qD₁ hfirst qCT qDT
    hCf rfl hDf rfl

private theorem shared_flag_comparison {B T U BK : Scheme.{u}}
    (κ : T ⟶ B) (τ : U ⟶ T) (ρ : BK ⟶ U) (σ : BK ⟶ T) (η : BK ⟶ B)
    (hρ : ρ ≫ τ = σ) (hσ : σ ≫ κ = η)
    (F : Over B) (FK : Over BK) (qF : FK.left ⟶ F.left)
    (hF : IsPullback qF FK.hom F.hom η) :
    ∃ qFT : FK.left ⟶ pullback τ (pullback.fst κ F.hom),
      IsPullback qFT FK.hom (pullback.fst τ (pullback.fst κ F.hom)) ρ ∧
      qFT ≫ pullback.fst τ (pullback.fst κ F.hom) = FK.hom ≫ ρ ∧
      qFT ≫ pullback.snd τ (pullback.fst κ F.hom) ≫ pullback.snd κ F.hom = qF := by
  obtain ⟨q₁, _h₁f, h₁s, h₁⟩ := source_scalar_square κ σ η FK.hom F.hom qF hσ hF
  obtain ⟨q₂, h₂f, h₂s, h₂⟩ := source_scalar_square τ ρ σ FK.hom
    (pullback.fst κ F.hom) q₁ hρ h₁
  have hs : q₂ ≫ pullback.snd τ (pullback.fst κ F.hom) ≫
      pullback.snd κ F.hom = qF :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ pullback.snd κ F.hom) h₂s).trans h₁s)
  exact ⟨q₂, h₂, h₂f, hs⟩

/-- A finite family of reduced-word endpoints and given Schubert inclusions
has proper arithmetic endpoints and closed inclusions into one shared scalar
flag model. All source, target, flag and endpoint comparisons retain their
original maps through the two specified coefficient projections. -/
theorem exists_word_endpoint_diagram
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {I : Type v} [Finite I] (G : ReductiveGroupData K)
    (words : I → List G.rootBase.support)
    (hred : ∀ i, (weylCoxeterSystem G.rootBase).IsReduced (words i))
    (S : Subalgebra ℤ K) (hS : S.FG) (start : CoefficientStage S)
    (D : I → Over (Spec (.of S))) (F : Over (Spec (.of S)))
    [∀ i, LocallyOfFinitePresentation (D i).hom] [∀ i, IsSeparated (D i).hom]
    (j : ∀ i, D i ⟶ F) [∀ i, IsClosedImmersion (j i).left]
    (qD : ∀ i, (schubertVariety G (simpleWeylWord G.rootBase (words i))).scheme ⟶ (D i).left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hD : ∀ i, IsPullback (qD i)
      (schubertVariety G (simpleWeylWord G.rootBase (words i))).toSpec (D i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hj : ∀ i, qD i ≫ (j i).left =
      (schubertInclusion G (simpleWeylWord G.rootBase (words i))).left ≫ qF) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k)
      (A : I → Over (Spec (.of k.val)))
      (qA : ∀ i, bsdhScheme G (words i) ⟶ (A i).left)
      (l : CoefficientStage k.val)
      (f : ∀ i, stageScalarModel k.val (A i).hom l ⟶
        stageScalarModel k.val (stageScalarModel S (D i).hom k).hom l)
      (mA : ∀ i, bsdhScheme G (words i) ⟶ (stageScalarModel k.val (A i).hom l).left)
      (mD : ∀ i, (schubertVariety G (simpleWeylWord G.rootBase (words i))).scheme ⟶
        (stageScalarModel k.val (stageScalarModel S (D i).hom k).hom l).left)
      (mF : (flagVariety G).scheme ⟶
        (stageScalarModel k.val (stageScalarModel S F.hom k).hom l).left),
      IsPullback mF (flagVariety G).toSpec
        (stageScalarModel k.val (stageScalarModel S F.hom k).hom l).hom
        (Spec.map (CommRingCat.ofHom (algebraMap l.val K))) ∧
      mF ≫ pullback.snd _ (stageScalarModel S F.hom k).hom ≫
        pullback.snd _ F.hom = qF ∧
      ∀ i, (IsProper (A i).hom ∧ Smooth (A i).hom ∧
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
          IsProper (f i).left) ∧
        let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
        let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom)
        IsClosedImmersion (chosenScalarArrow τ (chosenScalarArrow κ (j i))).left ∧
        mD i ≫ (chosenScalarArrow τ (chosenScalarArrow κ (j i))).left =
          (schubertInclusion G (simpleWeylWord G.rootBase (words i))).left ≫ mF := by
  classical
  obtain ⟨k, hk, A, qA, l, f, mA, mD, h⟩ :=
    exists_word_endpoint_arrows G words hred S hS start D qD hD
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap l.val K))
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k.val K))
  let η := Spec.map (CommRingCat.ofHom (algebraMap S K))
  obtain ⟨mF, hmF, hmFf, hmFs⟩ := shared_flag_comparison κ τ ρ σ η
    (coefficient_triangle k.val l.val l.property.2)
    (coefficient_triangle S k.val k.property.2) F (flagVariety G).toOver qF hF
  refine ⟨k, hk, A, qA, l, f, mA, mD, mF, hmF, hmFs, ?_⟩
  intro i
  have hi := h i
  rcases hi with ⟨_hpA, _hsA, _hcA, _hA, _hmA, hmD, _hprojA, hprojD,
    _hendpoint, _hbase, _hproper⟩
  have htriangle := nested_scalar_triangle κ τ ρ (j i)
    (schubertInclusion G (simpleWeylWord G.rootBase (words i))) (qD i) qF (hj i)
    (mD i) mF hmD.w hmFf
    ((Category.assoc _ _ _).trans hprojD)
    ((Category.assoc _ _ _).trans hmFs)
  let : IsClosedImmersion (chosenScalarArrow κ (j i)).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (scalarArrow_isPullback κ (j i)).flip inferInstance
  have hclosed : IsClosedImmersion (chosenScalarArrow τ (chosenScalarArrow κ (j i))).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (scalarArrow_isPullback τ (chosenScalarArrow κ (j i))).flip inferInstance
  exact ⟨h i, hclosed, htriangle⟩

end SchubertGeometry
