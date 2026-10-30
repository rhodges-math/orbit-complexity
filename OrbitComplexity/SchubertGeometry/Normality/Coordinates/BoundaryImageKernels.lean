import OrbitComplexity.SchubertGeometry.Normality.Coordinates.ChosenChartRetractions
import OrbitComplexity.FrobeniusSplitting.Normality.Images.RetractionKernels
import Batteries.Tactic.Lint

/-! # Image kernels on chosen arithmetic source covers

A surjection to a reduced field scheme gives retractions of the chosen
arithmetic section maps at a coefficient stage. These retractions retain image
kernels after every extension of scalars, including residue fields.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u v

private def kernelExtensionData {R M P : Type u}
    [CommRing R] [CommRing M] [CommRing P] [Algebra R M] [Algebra R P]
    (g : M →ₐ[R] P) : Prop :=
  ∀ (L : Type u) [CommRing L] [Algebra R L]
    (A : Type u) [CommRing A] [Algebra R A] (b : A →ₐ[R] M),
    RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (g.comp b)).toRingHom =
      RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L b).toRingHom

private theorem kernelExtensionData_of_retraction {R M P : Type u}
    [CommRing R] [CommRing M] [CommRing P] [Algebra R M] [Algebra R P]
    (g : M →ₐ[R] P) (r : P →ₗ[R] M)
    (hr : r.comp g.toLinearMap = LinearMap.id) : kernelExtensionData g := by
  intro L _ _ A _ _ b
  exact tensor_kernel_comp_of_retraction b g r hr L

private theorem kernelExtensionData_enlarge {S R T M P : Type u}
    [CommRing S] [CommRing R] [CommRing T] [CommRing M] [CommRing P]
    [Algebra S R] [Algebra R T] [Algebra S T] [IsScalarTower S R T]
    [Algebra S M] [Algebra S P]
    (g : M →ₐ[S] P) (r : R ⊗[S] P →ₗ[R] R ⊗[S] M)
    (hr : r.comp (Algebra.TensorProduct.lTensor (S := R) R g).toLinearMap =
      LinearMap.id) :
    kernelExtensionData (Algebra.TensorProduct.lTensor (S := T) T g) := by
  obtain ⟨q, hq⟩ := retraction_enlarge (T := T) g r hr
  exact kernelExtensionData_of_retraction
    (Algebra.TensorProduct.lTensor (S := T) T g) q hq

private noncomputable def boundaryChartArrow {R : Type u} [CommRing R]
    (C D : Over (Spec (.of R))) (e : C ⟶ D) (U : D.left.Opens) :
    Over.mk ((e.left ⁻¹ᵁ U).ι ≫ C.hom) ⟶ Over.mk (U.ι ≫ D.hom) :=
  Over.homMk (e.left ∣_ U) (by
    change (e.left ∣_ U) ≫ (U.ι ≫ D.hom) =
      (e.left ⁻¹ᵁ U).ι ≫ C.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w e])

private noncomputable def boundaryCoverMap {R : Type u} [CommRing R]
    (C D : Over (Spec (.of R))) (e : C ⟶ D) (U : D.left.Opens)
    (V : (e.left ⁻¹ᵁ U).toScheme.OpenCover.{u}) :
    ((algΓ (.of R)).obj (Over.mk (U.ι ≫ D.hom))).unop →ₐ[R]
      (∀ j, ((algΓ (.of R)).obj
        (Over.mk (V.f j ≫ ((e.left ⁻¹ᵁ U).ι ≫ C.hom)))).unop) :=
  affineCoverSectionMap (boundaryChartArrow C D e U) V

/-- The section maps of a chosen source cover retain their image kernels over
all scalar extensions above a prescribed finite coefficient ring. -/
theorem exists_boundary_image_kernels {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {I : Type v} [Finite I]
    (C D : Over (Spec (.of S))) (X Y : Over (Spec (.of K)))
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation D.hom]
    (e : C ⟶ D) (f : X ⟶ Y)
    [QuasiCompact e.left] [QuasiCompact f.left]
    [Surjective f.left] [IsReduced Y.left]
    (qC : X.left ⟶ C.left) (qD : Y.left ⟶ D.left)
    (hC : IsPullback qC X.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD Y.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hsquare : qC ≫ e.left = f.left ≫ qD)
    (W : I → D.left.Opens) (hW : ∀ i, IsAffineOpen (W i))
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ V : ∀ i, (e.left ⁻¹ᵁ W i).toScheme.OpenCover.{u},
      (∀ i, Finite (V i).I₀) ∧ (∀ i j, IsAffine ((V i).X j)) ∧
      ∃ R : Subalgebra ℤ K, R.FG ∧ start ≤ R ∧ ∃ hSR : S ≤ R,
        let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
        ∀ i, kernelExtensionData
          (Algebra.TensorProduct.lTensor (S := R) R
            (boundaryCoverMap C D e (W i) (V i))) := by
  obtain ⟨V, hfinite, hAffine, R, hR, hSR, hr⟩ :=
    exists_chosen_chart_retractions S hS C.hom D.hom X.hom Y.hom
      e.left f.left (Over.w e) (Over.w f) qC qD hC hD hsquare W hW
  let T : Subalgebra ℤ K := R ⊔ start
  have hST : S ≤ T := hSR.trans le_sup_left
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : Algebra R T :=
    (Subalgebra.inclusion (show R ≤ T from le_sup_left)).toAlgebra
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨V, hfinite, hAffine, T, hR.sup hstart, le_sup_right, hST, ?_⟩
  dsimp only
  intro i
  obtain ⟨r, hri⟩ := hr i
  exact kernelExtensionData_enlarge (T := T)
    (boundaryCoverMap C D e (W i) (V i)) r hri

end SchubertGeometry
