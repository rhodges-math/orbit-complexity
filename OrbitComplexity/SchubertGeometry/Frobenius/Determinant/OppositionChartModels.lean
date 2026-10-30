import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomialChart
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarPolynomialSquare
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.TensorCancellation
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Transverse chart maps into a flag model

The polynomial chart descends between the specified coefficient models.
Its scalar comparisons and its map into the same flag model are retained.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting GroupActions ReductiveGroups

namespace SchubertGeometry.DeterminantSection

open scoped TensorProduct
open private chartAlgebra from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial
open private FrobeniusSplitting.RetainedCharacter.scalarMap
  FrobeniusSplitting.RetainedCharacter.scalarMap_factor from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments

open private FrobeniusSplitting.modelComparison
  FrobeniusSplitting.modelComparison_projection
  FrobeniusSplitting.underlyingIso from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares
open private FrobeniusSplitting.scalarLeg_fst from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelStageMaps
open private FrobeniusSplitting.scalarLeg_snd from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent

private theorem scalar_cartesian {B T U X Y : Scheme.{u}}
    (κ : T ⟶ B) (ρ : T ⟶ U) (β : U ⟶ B) (hκ : ρ ≫ β = κ)
    (a : Y ⟶ B) (x : X ⟶ T) (q : X ⟶ Y)
    (h : IsPullback q x a κ) (n : X ⟶ pullback β a)
    (hn : n ≫ pullback.snd β a = q)
    (hb : n ≫ pullback.fst β a = x ≫ ρ) :
    IsPullback n x (pullback.fst β a) ρ := by
  have houter : IsPullback (n ≫ pullback.snd β a) x a (ρ ≫ β) := by
    rw [hn, hκ]
    exact h
  exact houter.of_right hb (IsPullback.of_hasPullback β a).flip

private theorem chart_triangle {C : Type*} [Category C]
    {X Y A B P Q : C} (α : X ≅ A) (β : Y ≅ B)
    (f : X ⟶ Y) (g : A ⟶ B) (i : P ⟶ Q) (u : A ⟶ P) (v : B ⟶ Q)
    (hg : g = α.inv ≫ f ≫ β.hom) (h : u ≫ i = g ≫ v) :
    (α.hom ≫ u) ≫ i = f ≫ (β.hom ≫ v) := by
  calc
    _ = α.hom ≫ (u ≫ i) := Category.assoc _ _ _
    _ = α.hom ≫ (g ≫ v) := congrArg (α.hom ≫ ·) h
    _ = α.hom ≫ ((α.inv ≫ f ≫ β.hom) ≫ v) := by rw [hg]
    _ = _ := by simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

private theorem composite_projection {C : Type*} [Category C] {X A B D : C}
    (a : X ⟶ A) (u : A ⟶ B) (v : B ⟶ D) (r : A ⟶ D) (q : X ⟶ D)
    (hu : u ≫ v = r) (ha : a ≫ r = q) : (a ≫ u) ≫ v = q :=
  (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) hu).trans ha)

private theorem composite_base {C : Type*} [Category C] {X A B D E : C}
    (a : X ⟶ A) (u : A ⟶ B) (v : B ⟶ E) (r : A ⟶ D) (q : X ⟶ D)
    (ρ : D ⟶ E) (hu : u ≫ v = r ≫ ρ) (ha : a ≫ r = q) :
    (a ≫ u) ≫ v = q ≫ ρ :=
  (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) hu).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ρ) ha)))

private theorem retain_chart_map
    {K : Type u} [kComm : CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    (C F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [LocallyOfFinitePresentation F.hom]
    (X Y : Over (Spec (.of K))) (f : X ⟶ Y)
    (qC : X.left ⟶ C.left) (qF : Y.left ⟶ F.left)
    (hC : IsPullback qC X.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF Y.hom F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t)
      (it : stageScalarModel S C.hom t ⟶ stageScalarModel S F.hom t)
      (qCt : X.left ⟶ (stageScalarModel S C.hom t).left)
      (qFt : Y.left ⟶ (stageScalarModel S F.hom t).left),
      IsPullback qCt X.hom (stageScalarModel S C.hom t).hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
      IsPullback qFt Y.hom (stageScalarModel S F.hom t).hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
      qCt ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
        C.hom = qC ∧
      qFt ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
        F.hom = qF ∧ f.left ≫ qFt = qCt ≫ it.left := by
  let α : X ≅ genericScalarModel S C.hom :=
    FrobeniusSplitting.modelComparison
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) C qC hC
  let β : Y ≅ genericScalarModel S F.hom :=
    FrobeniusSplitting.modelComparison
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) F qF hF
  let g : genericScalarModel S C.hom ⟶ genericScalarModel S F.hom :=
    α.inv ≫ f ≫ β.hom
  obtain ⟨r, ir, hir⟩ := @exists_model_morphism.{u} K kComm S hS C.left F.left
    inferInstance inferInstance C.hom F.hom inferInstance g
  let t : CoefficientStage S :=
    ⟨r.val ⊔ start.val, r.property.1.sup start.property.1,
      r.property.2.trans le_sup_left⟩
  have hrt : r ≤ t := by
    change r.val ≤ r.val ⊔ start.val
    exact le_sup_left
  have hst : start ≤ t := by
    change start.val ≤ r.val ⊔ start.val
    exact le_sup_right
  let it := @extendModelMorphism.{u} K kComm S C.left F.left C.hom F.hom r t hrt ir
  let qCt := α.hom.left ≫ (modelScalarCone S C.hom).π.app (op t)
  let qFt := β.hom.left ≫ (modelScalarCone S F.hom).π.app (op t)
  have hct : qCt ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
      C.hom = qC := by
    exact composite_projection α.hom.left _ _ _ qC
      (FrobeniusSplitting.scalarLeg_snd S C.hom t)
      (FrobeniusSplitting.modelComparison_projection _ C qC hC)
  have hft : qFt ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
      F.hom = qF := by
    exact composite_projection β.hom.left _ _ _ qF
      (FrobeniusSplitting.scalarLeg_snd S F.hom t)
      (FrobeniusSplitting.modelComparison_projection _ F qF hF)
  have hcb : qCt ≫ (stageScalarModel S C.hom t).hom =
      X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap t.val K)) := by
    exact composite_base α.hom.left _ _ _ X.hom _
      (FrobeniusSplitting.scalarLeg_fst S C.hom t) α.hom.w
  have hfb : qFt ≫ (stageScalarModel S F.hom t).hom =
      Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap t.val K)) := by
    exact composite_base β.hom.left _ _ _ Y.hom _
      (FrobeniusSplitting.scalarLeg_fst S F.hom t) β.hom.w
  have hscalar : Spec.map (CommRingCat.ofHom (algebraMap t.val K)) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom) =
        Spec.map (CommRingCat.ofHom (algebraMap S K)) := by
    rw [← Spec.map_comp]
    rfl
  refine ⟨t, hst, it, qCt, qFt, ?_, ?_, hct, hft, ?_⟩
  · exact scalar_cartesian _ _ _ hscalar C.hom X.hom qC hC qCt hct hcb
  · exact scalar_cartesian _ _ _ hscalar F.hom Y.hom qF hF qFt hft hfb
  · have hi := @extendModelMorphism_baseChange.{u} K kComm S C.left F.left
      C.hom F.hom r t hrt ir g hir
    exact (chart_triangle
      (FrobeniusSplitting.underlyingIso α) (FrobeniusSplitting.underlyingIso β)
      f.left g.left it.left ((modelScalarCone S C.hom).π.app (op t))
      ((modelScalarCone S F.hom).π.app (op t)) rfl hi).symm


variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K)

/-- The once-chosen coefficient model gives a polynomial tensor chart mapping
into the scalar extension of the flag model, with both comparisons retained. -/
theorem exists_opposition_chart_map
    (r : G.rootBase.support) (S : Subalgebra ℤ K) (hS : S.FG)
    (B : Type u) [bComm : CommRing B] [sB : Algebra S B]
    (e : K ⊗[S] B ≃ₐ[K] chartAlgebra G r)
    (F : Over (Spec (.of S))) [fFP : LocallyOfFinitePresentation F.hom]
    (qF : (flagVariety G).toOver.left ⟶ F.left)
    (hF : IsPullback qF (flagVariety G).toOver.hom F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t),
      letI sT : Algebra S t.val := (Subalgebra.inclusion t.property.2).toAlgebra
      letI tower : IsScalarTower S t.val K :=
        Subalgebra.inclusion.isScalarTower_right t.property.2 K
      let coefficientMap : t.val ⊗[S] B →+* chartAlgebra G r :=
        @FrobeniusSplitting.RetainedCharacter.scalarMap
        S t.val K B (chartAlgebra G r)
        (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing t.val))
        kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
        sT (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra t.val K))
        sB (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e
      let H : Over (Spec (.of t.val)) :=
        @polynomialModel.{u} t.val (t.val ⊗[S] B)
          (inferInstanceAs (CommRing t.val))
          (inferInstanceAs (CommRing (t.val ⊗[S] B)))
          (inferInstanceAs (Algebra t.val (t.val ⊗[S] B)))
      ∃ (i : H ⟶ stageScalarModel S F.hom t)
        (qFt : (flagVariety G).toOver.left ⟶ (stageScalarModel S F.hom t).left),
        IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom coefficientMap)))
          (affineVariety K (Polynomial (chartAlgebra G r))).toOver.hom H.hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
        IsPullback qFt (flagVariety G).toOver.hom (stageScalarModel S F.hom t).hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
        qFt ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          F.hom = qF ∧
        (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left ≫ qFt =
          Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom coefficientMap)) ≫ i.left := by
  let C : Over (Spec (.of S)) :=
    @polynomialModel.{u} S B (inferInstanceAs (CommRing S)) bComm sB
  have cCompact : CompactSpace C.left := by
    change CompactSpace (Spec (.of (Polynomial B)))
    infer_instance
  have cQS : QuasiSeparatedSpace C.left := by
    change QuasiSeparatedSpace (Spec (.of (Polynomial B)))
    infer_instance
  have hCAll := @exists_scalar_polynomial_square.{u}
    S K B (chartAlgebra G r) (inferInstanceAs (CommRing S)) kField.toCommRing
    bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    (inferInstanceAs (Algebra S K)) sB (inferInstanceAs (Algebra K (chartAlgebra G r))) e
  obtain ⟨_, _, _, hC⟩ := hCAll
  have hdescent :=
    @retain_chart_map.{u} K kField.toCommRing S hS C F cCompact cQS fFP
      (affineVariety K (Polynomial (chartAlgebra G r))).toOver (flagVariety G).toOver
      (@oppositionPolynomialMap.{u} K kField kClosed kZero G r)
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (e.toRingHom.comp
          (Algebra.TensorProduct.includeRight : B →ₐ[S] K ⊗[S] B).toRingHom))))
      qF hC hF start
  obtain ⟨t, ht, it, qCt, qFt, hCt, hFt, hOldC, hOldF, hchart⟩ := hdescent
  refine ⟨t, ht, ?_⟩
  let sT : Algebra S t.val := (Subalgebra.inclusion t.property.2).toAlgebra
  let tower : IsScalarTower S t.val K :=
    Subalgebra.inclusion.isScalarTower_right t.property.2 K
  intro coefficientMap H
  have hLiteral := @exists_polynomial_tensor_chart.{u}
    S t.val K B (chartAlgebra G r)
    (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing t.val)) kField.toCommRing
    bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sT (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra t.val K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e
    (stageScalarModel S C.hom t) (stageScalarModel S F.hom t)
    (pullback.snd _ C.hom) (IsPullback.of_hasPullback _ C.hom).flip
    (flagVariety G).toOver.left
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left
    qCt qFt it hOldC hCt.w hchart
  obtain ⟨i, hH, hi, _⟩ := hLiteral
  exact ⟨i, qFt, hH, hFt, hOldF, hi⟩

end SchubertGeometry.DeterminantSection
