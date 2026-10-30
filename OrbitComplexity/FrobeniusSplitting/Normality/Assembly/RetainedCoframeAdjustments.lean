import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.AdjustedFrameSquares
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareComposition
import Batteries.Tactic.Lint

/-! # Retained coframe adjustments on fixed affine charts

A finite family of coframe ratios descends to units on scalar extensions of
the given affine charts. The units adjust the pulled original coframes, and
their specified field comparisons become the prescribed coframes of the
same line. The chart maps continue to target the original scheme.
-/

set_option autoImplicit false

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting.CharacterLine
open scoped TensorProduct

namespace FrobeniusSplitting.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def scalarMap {S R K M A : Type u}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra S K] [Algebra R K] [Algebra S M] [Algebra K A]
    [IsScalarTower S R K] (e : K ⊗[S] M ≃ₐ[K] A) : R ⊗[S] M →+* A :=
  e.toRingHom.comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
    (AlgHom.id S M)).toRingHom

private theorem scalarMap_factor {S R K M A : Type u}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra S K] [Algebra R K] [Algebra S M] [Algebra K A]
    [IsScalarTower S R K] (e : K ⊗[S] M ≃ₐ[K] A) (v : M →+* A)
    (he : ∀ x, e ((1 : K) ⊗ₜ[S] x) = v x) :
    (scalarMap (R := R) e).comp
      (Algebra.TensorProduct.includeRight : M →ₐ[S] R ⊗[S] M).toRingHom = v := by
  ext x
  change e (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
    (AlgHom.id S M) ((1 : R) ⊗ₜ[S] x)) = v x
  rw [Algebra.TensorProduct.map_tmul, map_one]
  exact he x

private def extendedFrame {Y : Scheme.{u}} {M B : Type u}
    [CommRing M] [CommRing B] (ι : M →+* B) (j : Spec (.of M) ⟶ Y)
    (L : Y.Modules)
    (E : (Scheme.Modules.pullback j).obj L ≅ unitModule (Spec (.of M))) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι) ≫ j)).obj L ≅
      unitModule (Spec (.of B)) :=
  ((pullbackComp (Spec.map (CommRingCat.ofHom ι)) j).app L).symm ≪≫
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).mapIso E ≪≫
      pullbackObjUnitIso (Spec.map (CommRingCat.ofHom ι))

private theorem chart_composition {P B C Y Z : Scheme.{u}}
    (q : Z ⟶ Y) (a : P ⟶ Z) (c : C ⟶ Y) (u : P ⟶ B) (v : B ⟶ C)
    (k : P ⟶ C) (hk : u ≫ v = k)
    (h : u ≫ (v ≫ c) = a ≫ q) (h₀ : k ≫ c = a ≫ q) (L : Y.Modules)
    (E : (Scheme.Modules.pullback c).obj L ≅ unitModule C) :
    squareFrameIso q a (v ≫ c) u h L
      (((pullbackComp v c).app L).symm ≪≫
        (Scheme.Modules.pullback v).mapIso E ≪≫ pullbackObjUnitIso v) =
      squareFrameIso q a c k h₀ L E := by
  subst k
  exact squareFrameIso_chart_comp q a c u v h h₀ L E

section Family

variable {S R K : Type u} [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    {I : Type v} (M A : I → Type u)
    [∀ i, CommRing (M i)] [∀ i, Algebra S (M i)]
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    (e : ∀ i, K ⊗[S] M i ≃ₐ[K] A i) (v₀ : ∀ i, M i →+* A i)
    {Y YK : Scheme.{u}} (q : YK ⟶ Y) (L : Y.Modules)
    (j : ∀ i, Spec (.of (M i)) ⟶ Y) (a : ∀ i, Spec (.of (A i)) ⟶ YK)
    (hscalar : ∀ i, Spec.map (CommRingCat.ofHom (v₀ i)) ≫ j i = a i ≫ q)
    (E : ∀ i, (Scheme.Modules.pullback (j i)).obj L ≅ unitModule (Spec (.of (M i))))
    (F : ∀ i, (Scheme.Modules.pullback (a i)).obj ((Scheme.Modules.pullback q).obj L) ≅
      unitModule (Spec (.of (A i))))

private def adjustedFamilyData : Prop :=
  ∃ d : ∀ i, (R ⊗[S] M i)ˣ,
    (∀ i, scalarMap (R := R) (e i) (d i : R ⊗[S] M i) =
      (affineCoframeUnit (A i)
        (squareFrameIso q (a i) (j i) (Spec.map (CommRingCat.ofHom (v₀ i)))
          (hscalar i) L (E i)) (F i) : A i)) ∧
    (∀ i n, scalarMap (R := R) (e i) ((d i : R ⊗[S] M i) ^ n) =
      (affineCoframeUnit (A i)
        (squareFrameIso q (a i) (j i) (Spec.map (CommRingCat.ofHom (v₀ i)))
          (hscalar i) L (E i)) (F i) : A i) ^ n) ∧
    ∀ i,
      let ι := (Algebra.TensorProduct.includeRight : M i →ₐ[S] R ⊗[S] M i).toRingHom
      ∃ h : Spec.map (CommRingCat.ofHom (scalarMap (R := R) (e i))) ≫
          (Spec.map (CommRingCat.ofHom ι) ≫ j i) = a i ≫ q,
        squareFrameIso q (a i) (Spec.map (CommRingCat.ofHom ι) ≫ j i)
          (Spec.map (CommRingCat.ofHom (scalarMap (R := R) (e i)))) h L
          (adjustedCoframe (extendedFrame ι (j i) L (E i)) (d i)) = F i

private theorem adjustments_of_units
    (he : ∀ i x, e i ((1 : K) ⊗ₜ[S] x) = v₀ i x)
    (d : ∀ i, (R ⊗[S] M i)ˣ)
    (hd : ∀ i, scalarMap (R := R) (e i) (d i : R ⊗[S] M i) =
      (affineCoframeUnit (A i)
        (squareFrameIso q (a i) (j i) (Spec.map (CommRingCat.ofHom (v₀ i)))
          (hscalar i) L (E i)) (F i) : A i))
    (hpow : ∀ i n, scalarMap (R := R) (e i) ((d i : R ⊗[S] M i) ^ n) =
      (affineCoframeUnit (A i)
        (squareFrameIso q (a i) (j i) (Spec.map (CommRingCat.ofHom (v₀ i)))
          (hscalar i) L (E i)) (F i) : A i) ^ n) :
    adjustedFamilyData (R := R) M A e v₀ q L j a hscalar E F := by
  refine ⟨d, hd, hpow, ?_⟩
  intro i
  let ι := (Algebra.TensorProduct.includeRight : M i →ₐ[S] R ⊗[S] M i).toRingHom
  let φ := scalarMap (R := R) (e i)
  have hmap : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ι) =
      Spec.map (CommRingCat.ofHom (v₀ i)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun z => Spec.map (CommRingCat.ofHom z))
      (scalarMap_factor (R := R) (e i) (v₀ i) (he i))
  have h : Spec.map (CommRingCat.ofHom φ) ≫
      (Spec.map (CommRingCat.ofHom ι) ≫ j i) = a i ≫ q := by
    rw [← Category.assoc, hmap]
    exact hscalar i
  refine ⟨h, ?_⟩
  apply adjustedCoframe_square φ q (a i)
    (Spec.map (CommRingCat.ofHom ι) ≫ j i) h L
    (extendedFrame ι (j i) L (E i)) (F i) (d i)
  have hframe := chart_composition q (a i) (j i)
    (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom ι))
    (Spec.map (CommRingCat.ofHom (v₀ i))) hmap h (hscalar i) L (E i)
  change squareFrameIso q (a i) (Spec.map (CommRingCat.ofHom ι) ≫ j i)
    (Spec.map (CommRingCat.ofHom φ)) h L (extendedFrame ι (j i) L (E i)) = _ at hframe
  change φ (d i : R ⊗[S] M i) = _
  rw [hframe]
  exact hd i

end Family

section Stages

variable {K : Type u} [Field K] (S : Subalgebra ℤ K)
    {I : Type v} (M A : I → Type u)
    [∀ i, CommRing (M i)] [∀ i, Algebra S (M i)]
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    (e : ∀ i, K ⊗[S] M i ≃ₐ[K] A i) (v₀ : ∀ i, M i →+* A i)
    {Y YK : Scheme.{u}} (q : YK ⟶ Y) (L : Y.Modules)
    (j : ∀ i, Spec (.of (M i)) ⟶ Y) (a : ∀ i, Spec (.of (A i)) ⟶ YK)
    (hscalar : ∀ i, Spec.map (CommRingCat.ofHom (v₀ i)) ≫ j i = a i ≫ q)
    (E : ∀ i, (Scheme.Modules.pullback (j i)).obj L ≅ unitModule (Spec (.of (M i))))
    (F : ∀ i, (Scheme.Modules.pullback (a i)).obj ((Scheme.Modules.pullback q).obj L) ≅
      unitModule (Spec (.of (A i))))

/-- One coefficient stage retains the coframe units and their powers, and
identifies the adjusted scalar-chart coframes with the prescribed comparisons. -/
def coframeAdjustmentStage (R : Subalgebra ℤ K) (hSR : S ≤ R) : Prop :=
  letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  R.FG ∧ adjustedFamilyData (R := R) M A e v₀ q L j a hscalar E F

/-- Finitely many pairs of specified coframes admit adjusted scalar-chart
coframes over a single coefficient extension of the original models. -/
theorem exists_retained_coframe_adjustments [Finite I] (hS : S.FG)
    [∀ i, Module.Flat S (M i)] [∀ i, Algebra.FinitePresentation S (M i)]
    (he : ∀ i x, e i ((1 : K) ⊗ₜ[S] x) = v₀ i x) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      coframeAdjustmentStage S M A e v₀ q L j a hscalar E F R hSR := by
  choose n m hP using fun i => Algebra.Presentation.exists_presentation_fin S (M i)
  let Q : ∀ i, Algebra.Presentation S (M i) (Fin (n i)) (Fin (m i)) :=
    fun i => Classical.choice (hP i)
  obtain ⟨R, hSR, hR⟩ := exists_frame_unit_retention S hS M A e
    (fun i => Fin (n i)) (fun i => Fin (m i)) Q
    (fun i => (Scheme.Modules.pullback (a i)).obj ((Scheme.Modules.pullback q).obj L))
    (fun i => squareFrameIso q (a i) (j i) (Spec.map (CommRingCat.ofHom (v₀ i)))
      (hscalar i) L (E i)) F
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  obtain ⟨hfg, d, hd, hpow⟩ := hR
  refine ⟨R, hSR, hfg, ?_⟩
  exact adjustments_of_units M A e v₀ q L j a hscalar E F he d hd hpow

end Stages

end FrobeniusSplitting.RetainedCharacter
