import OrbitComplexity.SchubertGeometry.Normality.Coordinates.BoundaryImageKernels
import OrbitComplexity.SchubertGeometry.Normality.Coordinates.ChosenCoverCoordinates
import OrbitComplexity.FrobeniusSplitting.Normality.Retractions.RetractionEnlargement

/-! # Injectivity on field coordinates from retained image kernels

Kernel preservation at a coefficient stage gives injectivity after every
further scalar extension. The section comparisons for a chosen affine cover
transfer this injectivity to the section map of the prescribed scheme morphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

open private kernelExtensionData from
  OrbitComplexity.SchubertGeometry.Normality.Coordinates.BoundaryImageKernels
open private cancel_map_square from
  OrbitComplexity.FrobeniusSplitting.Normality.Retractions.RetractionEnlargement

namespace SchubertGeometry

universe u

private theorem tensor_injective_of_kernels {R M P : Type u}
    [CommRing R] [CommRing M] [CommRing P] [Algebra R M] [Algebra R P]
    (g : M →ₐ[R] P) (h : kernelExtensionData g)
    (L : Type u) [CommRing L] [Algebra R L] :
    Function.Injective (Algebra.TensorProduct.lTensor (S := L) L g) := by
  have hi : Algebra.TensorProduct.lTensor (S := L) L (AlgHom.id R M) =
      AlgHom.id L (L ⊗[R] M) := by
    ext a
    rfl
  have hk := h L M (AlgHom.id R M)
  rw [AlgHom.comp_id, hi] at hk
  apply (RingHom.injective_iff_ker_eq_bot
    (Algebra.TensorProduct.lTensor (S := L) L g).toRingHom).mpr
  rw [hk]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (fun _ _ h ↦ h)

private theorem scalar_injective_of_kernels {S R L M P : Type u}
    [CommRing S] [CommRing R] [CommRing L] [CommRing M] [CommRing P]
    [Algebra S R] [Algebra R L] [Algebra S L] [IsScalarTower S R L]
    [Algebra S M] [Algebra S P]
    (g : M →ₐ[S] P)
    (h : kernelExtensionData (Algebra.TensorProduct.lTensor (S := R) R g)) :
    Function.Injective (Algebra.TensorProduct.lTensor (S := L) L g) := by
  let cM : L ⊗[R] (R ⊗[S] M) ≃ₐ[L] L ⊗[S] M :=
    Algebra.TensorProduct.cancelBaseChange S R L L M
  let cP : L ⊗[R] (R ⊗[S] P) ≃ₐ[L] L ⊗[S] P :=
    Algebra.TensorProduct.cancelBaseChange S R L L P
  have hg := tensor_injective_of_kernels _ h L
  intro a b hab
  apply cM.symm.injective
  apply hg
  apply cP.injective
  rw [cancel_map_square, cancel_map_square]
  change (Algebra.TensorProduct.lTensor (S := L) L g) (cM (cM.symm a)) =
    (Algebra.TensorProduct.lTensor (S := L) L g) (cM (cM.symm b))
  simpa only [AlgEquiv.apply_symm_apply] using hab

private theorem injective_right_of_square {K M N A B : Type u}
    [CommRing K] [CommRing M] [CommRing N] [CommRing A] [CommRing B]
    [Algebra K M] [Algebra K N] [Algebra K A] [Algebra K B]
    (eM : M ≃ₐ[K] A) (eN : N ≃ₐ[K] B)
    (g : M →ₐ[K] N) (f : A →ₐ[K] B)
    (h : eN.toAlgHom.comp g = f.comp eM.toAlgHom)
    (hg : Function.Injective g) : Function.Injective f := by
  intro a b hab
  obtain ⟨a, rfl⟩ := eM.surjective a
  obtain ⟨b, rfl⟩ := eM.surjective b
  apply congrArg eM
  apply hg
  apply eN.injective
  exact (AlgHom.congr_fun h a).trans
    (hab.trans (AlgHom.congr_fun h b).symm)

private theorem appTop_injective_of_cover {K : Type u} [CommRing K]
    {X Y : Over (Spec (.of K))} (f : X ⟶ Y) (V : X.left.OpenCover.{u})
    (h : Function.Injective (affineCoverSectionMap f V)) :
    Function.Injective f.left.appTop.hom := by
  intro a b hab
  apply h
  funext j
  change (V.f j ≫ f.left).appTop.hom a = (V.f j ≫ f.left).appTop.hom b
  rw [Scheme.Hom.comp_appTop]
  change (V.f j).appTop.hom (f.left.appTop.hom a) =
    (V.f j).appTop.hom (f.left.appTop.hom b)
  rw [hab]

/-- Preserved affine-cover kernels make the prescribed scalar endpoint injective
on global sections, without any reducedness assumption on its target. -/
theorem chosen_cover_appTop_injective {S R K : Type u}
    [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    {X₀ Y₀ X Y : Scheme.{u}} [IsAffine Y₀]
    (x₀ : X₀ ⟶ Spec (.of S)) (y₀ : Y₀ ⟶ Spec (.of S))
    (x : X ⟶ Spec (.of K)) (y : Y ⟶ Spec (.of K))
    (f₀ : X₀ ⟶ Y₀) (f : X ⟶ Y)
    (hf₀ : f₀ ≫ y₀ = x₀) (hfK : f ≫ y = x)
    (qX : X ⟶ X₀) (qY : Y ⟶ Y₀)
    (hX : IsPullback qX x x₀
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY y y₀
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hf : f ≫ qY = qX ≫ f₀)
    (V : X₀.OpenCover.{u}) [Finite V.I₀]
    (hV : ∀ j, IsAffine (V.X j))
    (hker : kernelExtensionData (Algebra.TensorProduct.lTensor (S := R) R
      (affineCoverSectionMap (Over.homMk f₀ hf₀ : Over.mk x₀ ⟶ Over.mk y₀) V))) :
    Function.Injective f.appTop.hom := by
  classical
  obtain ⟨eM, eN, _, _, hsquare⟩ :=
    exists_chosen_cover_coordinates x₀ y₀ x y f₀ f hf₀ hfK qX qY hX hY hf V hV
  let fS : Over.mk x₀ ⟶ Over.mk y₀ := Over.homMk f₀ hf₀
  let fK : Over.mk x ⟶ Over.mk y := Over.homMk f hfK
  let VK := V.pullback₂ qX
  let N₀ (j : V.I₀) : Type u :=
    ((algΓ (.of S)).obj (Over.mk (V.f j ≫ x₀))).unop
  let := Fintype.ofFinite V.I₀
  let eP := (Algebra.TensorProduct.piRight S K K N₀).trans
    (AlgEquiv.piCongrRight eN)
  have hg := scalar_injective_of_kernels (L := K) (affineCoverSectionMap fS V) hker
  have hcov : Function.Injective (affineCoverSectionMap fK VK) :=
    injective_right_of_square eM eP _ _ hsquare hg
  exact appTop_injective_of_cover fK VK hcov

end SchubertGeometry
