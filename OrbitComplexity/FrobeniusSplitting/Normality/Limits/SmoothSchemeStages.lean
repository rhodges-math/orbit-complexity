import OrbitComplexity.FrobeniusSplitting.Normality.Models.FiniteModelAlignment
import OrbitComplexity.FrobeniusSplitting.Normality.Products.PointedFamilyHelpers
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.AffineScalarCoordinates
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateDiagrams
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelStageMaps
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Smooth scalar stages

A compact finitely presented model with smooth generic fibre becomes smooth at
a finite coefficient stage. Finite affine covers and their tensor coordinate
comparisons preserve the chosen model throughout the extensions.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace FrobeniusSplitting

universe u

open private free_model_family from
  OrbitComplexity.FrobeniusSplitting.Normality.Models.FiniteModelAlignment
open private coordinates_finitePresentation coordinates_smooth from
  OrbitComplexity.FrobeniusSplitting.Normality.CoordinateDiagrams

private theorem smooth_family_stage {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {I : Type u} [Finite I]
    (M A : I → Type u) [∀ i, CommRing (M i)] [∀ i, CommRing (A i)]
    [∀ i, Algebra S (M i)] [∀ i, Algebra K (A i)]
    [∀ i, Algebra.FinitePresentation S (M i)] [∀ i, Algebra.Smooth K (A i)]
    (E : ∀ i, K ⊗[S] M i ≃ₐ[K] A i) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      R.FG ∧ ∀ i, Algebra.Smooth R (R ⊗[S] M i) := by
  obtain ⟨T, hT, hST, hfree⟩ := free_model_family S hS M
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let MT (i : I) := T ⊗[S] M i
  let (i : I) : Module.Free T (MT i) := hfree i
  let (i : I) : Module.Flat T (MT i) := Module.Flat.of_free
  let (i : I) : Algebra.FinitePresentation T (MT i) := inferInstance
  let ET (i : I) : K ⊗[T] MT i ≃ₐ[K] A i :=
    (Algebra.TensorProduct.cancelBaseChange S T K K (M i)).trans (E i)
  obtain ⟨R, hTR, hR, hsm⟩ := exists_smooth_family_extension T hT MT A ET
  let : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
  let : Algebra S R := (Subalgebra.inclusion (hST.trans hTR)).toAlgebra
  let : IsScalarTower S T R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨R, hST.trans hTR, hR, ?_⟩
  intro i
  let : Algebra.Smooth R (R ⊗[T] MT i) := hsm i
  exact Algebra.Smooth.of_equiv (Algebra.TensorProduct.cancelBaseChange S T R R (M i))

private theorem smooth_of_tensor_charts {S R : Type u}
    [CommRing S] [CommRing R] [Algebra S R]
    {D : Scheme.{u}} (d : D ⟶ Spec (.of S)) {I : Type u}
    (U : I → D.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤) (Y : Over (Spec (.of R))) (q : Y.left ⟶ D)
    (hq : IsPullback q Y.hom d (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hsm : ∀ i,
      letI : Algebra S Γ((U i).toScheme, ⊤) :=
        (((U i).ι ≫ d).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
      Algebra.Smooth R (R ⊗[S] Γ((U i).toScheme, ⊤))) : Smooth Y.hom := by
  let : IsAffineHom q := MorphismProperty.of_isPullback
    (P := @IsAffineHom) hq.flip inferInstance
  let V (i : I) := q ⁻¹ᵁ U i
  have hVcover : (⨆ i, V i) = ⊤ := by
    have h := congrArg (fun O => q ⁻¹ᵁ O) hcover
    change (⨆ i, (TopologicalSpace.Opens.map q.base).obj (U i)) = ⊤
    simpa only [TopologicalSpace.Opens.map_iSup, TopologicalSpace.Opens.map_top,
      Function.comp_def] using h
  let : IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @AlgebraicGeometry.Smooth.{u}) (f := Y.hom) V hVcover
  intro i
  have hVi : IsAffineOpen (V i) := (hU i).preimage q
  let : IsAffine (U i).toScheme := hU i
  let : IsAffine (V i).toScheme := hVi
  let : Algebra S Γ((U i).toScheme, ⊤) :=
    (((U i).ι ≫ d).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : Algebra R Γ((V i).toScheme, ⊤) :=
    (((V i).ι ≫ Y.hom).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  have hchart : IsPullback (q ∣_ U i) ((V i).ι ≫ Y.hom) ((U i).ι ≫ d)
      (Spec.map (CommRingCat.ofHom (algebraMap S R))) :=
    (isPullback_morphismRestrict q (U i)).paste_vert hq
  obtain ⟨E, _, _, _⟩ := exists_affine_scalar_coordinates
    ((U i).ι ≫ d) ((V i).ι ≫ Y.hom) (q ∣_ U i) hchart
  let : Algebra.Smooth R (R ⊗[S] Γ((U i).toScheme, ⊤)) := hsm i
  have hnormal : Algebra.Smooth R Γ((V i).toScheme, ⊤) := Algebra.Smooth.of_equiv E
  have hring : ((((V i).ι ≫ Y.hom).appTop.hom).comp
      (Scheme.ΓSpecIso (.of R)).inv.hom).Smooth := hnormal
  have hring' := (RingHom.Smooth.respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (.of R)).inv ((V i).ι ≫ Y.hom).appTop).mp hring
  exact (HasRingHomProperty.iff_of_isAffine (P := @Smooth) (f := (V i).ι ≫ Y.hom)).mpr hring'

/-- A compact model of finite presentation with smooth generic fibre is smooth
after extension to a coefficient stage above any prescribed stage. -/
theorem exists_smooth_scalar_stage {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) (F : Over (Spec (.of S)))
    [CompactSpace F.left] [LocallyOfFinitePresentation F.hom]
    [Smooth (genericScalarModel S F.hom).hom] (start : CoefficientStage S) :
    ∃ t : CoefficientStage S, start ≤ t ∧ Smooth (stageScalarModel S F.hom t).hom := by
  classical
  obtain ⟨I, hI, U, hU, hcover⟩ := exists_finite_affine_opens F.left
  let : Finite I := hI
  let M (i : I) : Type u := Γ((U i).toScheme, ⊤)
  let (i : I) : Algebra S (M i) :=
    (((U i).ι ≫ F.hom).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let (i : I) : IsAffine (Over.mk ((U i).ι ≫ F.hom)).left := hU i
  let (i : I) : LocallyOfFinitePresentation (Over.mk ((U i).ι ≫ F.hom)).hom :=
    (inferInstance : LocallyOfFinitePresentation ((U i).ι ≫ F.hom))
  let (i : I) : Algebra.FinitePresentation S (M i) :=
    coordinates_finitePresentation (.of S) (Over.mk ((U i).ι ≫ F.hom))
  let Y := genericScalarModel S F.hom
  let β := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let q : Y.left ⟶ F.left := pullback.snd β F.hom
  have hq : IsPullback q Y.hom F.hom β := (IsPullback.of_hasPullback β F.hom).flip
  let : IsAffineHom q := MorphismProperty.of_isPullback
    (P := @IsAffineHom) hq.flip inferInstance
  let V (i : I) := q ⁻¹ᵁ U i
  let A (i : I) : Type u := Γ((V i).toScheme, ⊤)
  let (i : I) : Algebra K (A i) :=
    (((V i).ι ≫ Y.hom).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let (i : I) : IsAffine (Over.mk ((V i).ι ≫ Y.hom)).left := (hU i).preimage q
  let (i : I) : Smooth (Over.mk ((V i).ι ≫ Y.hom)).hom :=
    (inferInstance : Smooth ((V i).ι ≫ Y.hom))
  let (i : I) : Algebra.Smooth K (A i) :=
    coordinates_smooth (.of K) (Over.mk ((V i).ι ≫ Y.hom))
  have he (i : I) : Nonempty (K ⊗[S] M i ≃ₐ[K] A i) := by
    let : IsAffine (U i).toScheme := hU i
    have hchart : IsPullback (q ∣_ U i) ((V i).ι ≫ Y.hom) ((U i).ι ≫ F.hom) β :=
      (isPullback_morphismRestrict q (U i)).paste_vert hq
    obtain ⟨E, _, _, _⟩ := exists_affine_scalar_coordinates
      ((U i).ι ≫ F.hom) ((V i).ι ≫ Y.hom) (q ∣_ U i) hchart
    exact ⟨E⟩
  obtain ⟨R, hSR, hR, hsm⟩ := smooth_family_stage S hS M A (fun i => (he i).some)
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let r : CoefficientStage S := ⟨R, hR, hSR⟩
  let FR := stageScalarModel S F.hom r
  let qR : FR.left ⟶ F.left := pullback.snd
    (Spec.map (CommRingCat.ofHom (algebraMap S R))) F.hom
  have hqR : IsPullback qR FR.hom F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S R))) :=
    (IsPullback.of_hasPullback _ _).flip
  have hFR : Smooth FR.hom := smooth_of_tensor_charts F.hom U hU hcover FR qR hqR hsm
  obtain ⟨t, hrt, hstart⟩ := exists_ge_ge r start
  refine ⟨t, hstart, ?_⟩
  exact MorphismProperty.of_isPullback (P := @Smooth) (stageScalarCartesian S F.hom hrt) hFR

end FrobeniusSplitting
