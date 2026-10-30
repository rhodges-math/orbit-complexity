import OrbitComplexity.SchubertGeometry.Normality.Coordinates.BoundaryScalarCharts
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Arithmetic boundary image kernels on field fibres

A finite affine target cover and retained source-cover retractions give a
single coefficient stage at which every field endpoint is scheme-theoretically
dominant. Its composition with an ambient inclusion therefore has exactly the
kernel of that inclusion.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

open private kernelExtensionData boundaryCoverMap from
  OrbitComplexity.SchubertGeometry.Normality.Coordinates.BoundaryImageKernels

namespace SchubertGeometry

universe u v

private theorem scalar_endpoint_dominant {S R K : Type u}
    [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    (C D : Over (Spec (.of S))) (e : C ⟶ D)
    (X Y : Over (Spec (.of K))) (f : X ⟶ Y) [QuasiCompact f.left]
    (qX : X.left ⟶ C.left) (qY : Y.left ⟶ D.left)
    (hX : IsPullback qX X.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY Y.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hf : f.left ≫ qY = qX ≫ e.left)
    {I : Type v} (W : I → D.left.Opens) (hW : ∀ i, IsAffineOpen (W i))
    (hcover : ⨆ i, W i = ⊤)
    (V : ∀ i, (e.left ⁻¹ᵁ W i).toScheme.OpenCover.{u})
    (hfinite : ∀ i, Finite (V i).I₀)
    (hV : ∀ i j, IsAffine ((V i).X j))
    (hker : ∀ i, kernelExtensionData
      (Algebra.TensorProduct.lTensor (S := R) R (boundaryCoverMap C D e (W i) (V i)))) :
    IsSchemeTheoreticallyDominant f.left := by
  have : IsAffineHom qY := MorphismProperty.of_isPullback hY.flip inferInstance
  constructor
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun i ↦ ⟨qY ⁻¹ᵁ W i, (hW i).preimage qY⟩)
    (qY.iSup_preimage_eq_top hcover)
  intro i
  let := hfinite i
  simpa only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using
    boundary_scalar_kernel_zero C D e X Y f qX qY hX hY hf
      (W i) (hW i) (V i) (hV i) (hker i) ((hW i).preimage qY)

private theorem scalar_endpoint_kernel_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) [IsSchemeTheoreticallyDominant f] (j : Y ⟶ Z) :
    (f ≫ j).ker = j.ker := by
  rw [Scheme.Hom.ker_comp, f.ker_eq_bot, Scheme.IdealSheafData.map_bot]

/-- A coefficient stage retains the boundary image kernel after every field
specialization, for endpoints with the prescribed Cartesian comparisons. -/
theorem exists_boundary_field_kernels {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {I : Type v} [Finite I]
    (C D : Over (Spec (.of S))) (X Y : Over (Spec (.of K)))
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation D.hom]
    (e : C ⟶ D) (f : X ⟶ Y)
    [QuasiCompact e.left] [QuasiCompact f.left] [Surjective f.left] [IsReduced Y.left]
    (qC : X.left ⟶ C.left) (qD : Y.left ⟶ D.left)
    (hC : IsPullback qC X.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD Y.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hsquare : qC ≫ e.left = f.left ≫ qD)
    (W : I → D.left.Opens) (hW : ∀ i, IsAffineOpen (W i))
    (hcover : ⨆ i, W i = ⊤)
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ start ≤ R ∧ ∃ hSR : S ≤ R,
      ∀ (L : Type u) [Field L] [Algebra R L]
        (XL YL : Over (Spec (.of L))) (fL : XL ⟶ YL) [QuasiCompact fL.left]
        (qXL : XL.left ⟶ C.left) (qYL : YL.left ⟶ D.left)
        (_hXL : IsPullback qXL XL.hom C.hom
          (Spec.map (CommRingCat.ofHom
            ((algebraMap R L).comp (Subalgebra.inclusion hSR).toRingHom))))
        (_hYL : IsPullback qYL YL.hom D.hom
          (Spec.map (CommRingCat.ofHom
            ((algebraMap R L).comp (Subalgebra.inclusion hSR).toRingHom))))
        (_hfL : fL.left ≫ qYL = qXL ≫ e.left),
        IsSchemeTheoreticallyDominant fL.left ∧
          ∀ (Z : Scheme.{u}) (j : YL.left ⟶ Z), (fL.left ≫ j).ker = j.ker := by
  obtain ⟨V, hfinite, hV, R, hR, hstartR, hSR, hker⟩ :=
    exists_boundary_image_kernels S hS C D X Y e f qC qD hC hD hsquare W hW start hstart
  refine ⟨R, hR, hstartR, hSR, ?_⟩
  let : Algebra S R := (Subalgebra.inclusion hSR).toRingHom.toAlgebra
  dsimp only at hker
  intro L _ _ XL YL fL _ qXL qYL hXL hYL hfL
  let : Algebra S L :=
    ((algebraMap R L).comp (Subalgebra.inclusion hSR).toRingHom).toAlgebra
  let : IsScalarTower S R L := IsScalarTower.of_algebraMap_eq' rfl
  have hdom : IsSchemeTheoreticallyDominant fL.left :=
    scalar_endpoint_dominant C D e XL YL fL qXL qYL hXL hYL hfL
      W hW hcover V hfinite hV hker
  let : IsSchemeTheoreticallyDominant fL.left := hdom
  exact ⟨hdom, fun Z j ↦ scalar_endpoint_kernel_comp fL.left j⟩

end SchubertGeometry
