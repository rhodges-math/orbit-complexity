import OrbitComplexity.SchubertGeometry.Normality.Coordinates.BoundaryTensorCoordinates

/-! # Scalar endpoint kernels on affine target opens

Restricting the prescribed Cartesian square gives the coordinate comparisons
for each arithmetic target chart. Open-set equalities are proved before the
scheme maps are transported, so their section maps retain the same kernels.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

open private kernelExtensionData boundaryCoverMap from
  OrbitComplexity.SchubertGeometry.Normality.Coordinates.BoundaryImageKernels

namespace SchubertGeometry

universe u

private theorem endpoint_open_eq {X₀ Y₀ X Y : Scheme.{u}}
    (f₀ : X₀ ⟶ Y₀) (f : X ⟶ Y) (qX : X ⟶ X₀) (qY : Y ⟶ Y₀)
    (h : f ≫ qY = qX ≫ f₀) (U : Y₀.Opens) :
    f ⁻¹ᵁ (qY ⁻¹ᵁ U) = qX ⁻¹ᵁ (f₀ ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, h, Scheme.Hom.comp_preimage]

private theorem eqToHom_open_ι {X : Scheme.{u}} {U V : X.Opens}
    (h : U = V) :
    eqToHom (congrArg Scheme.Opens.toScheme h) ≫ V.ι = U.ι := by
  subst V
  simp

private noncomputable def scalarChartMap {X₀ Y₀ X Y : Scheme.{u}}
    (f₀ : X₀ ⟶ Y₀) (f : X ⟶ Y) (qX : X ⟶ X₀) (qY : Y ⟶ Y₀)
    (h : f ≫ qY = qX ≫ f₀) (U : Y₀.Opens) :
    (qX ⁻¹ᵁ (f₀ ⁻¹ᵁ U)).toScheme ⟶ (qY ⁻¹ᵁ U).toScheme :=
  eqToHom (congrArg Scheme.Opens.toScheme (endpoint_open_eq f₀ f qX qY h U).symm) ≫
    f ∣_ (qY ⁻¹ᵁ U)

private theorem scalarChartMap_ι {X₀ Y₀ X Y : Scheme.{u}}
    (f₀ : X₀ ⟶ Y₀) (f : X ⟶ Y) (qX : X ⟶ X₀) (qY : Y ⟶ Y₀)
    (h : f ≫ qY = qX ≫ f₀) (U : Y₀.Opens) :
    scalarChartMap f₀ f qX qY h U ≫ (qY ⁻¹ᵁ U).ι =
      (qX ⁻¹ᵁ (f₀ ⁻¹ᵁ U)).ι ≫ f := by
  unfold scalarChartMap
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
    eqToHom_open_ι (endpoint_open_eq f₀ f qX qY h U).symm]

private theorem scalarChartMap_square {X₀ Y₀ X Y : Scheme.{u}}
    (f₀ : X₀ ⟶ Y₀) (f : X ⟶ Y) (qX : X ⟶ X₀) (qY : Y ⟶ Y₀)
    (h : f ≫ qY = qX ≫ f₀) (U : Y₀.Opens) :
    scalarChartMap f₀ f qX qY h U ≫ qY ∣_ U =
      qX ∣_ (f₀ ⁻¹ᵁ U) ≫ f₀ ∣_ U := by
  apply (cancel_mono U.ι).mp
  calc
    (scalarChartMap f₀ f qX qY h U ≫ qY ∣_ U) ≫ U.ι =
        scalarChartMap f₀ f qX qY h U ≫ (qY ⁻¹ᵁ U).ι ≫ qY := by
      rw [Category.assoc, morphismRestrict_ι]
    _ = (qX ⁻¹ᵁ (f₀ ⁻¹ᵁ U)).ι ≫ f ≫ qY := by
      rw [← Category.assoc, scalarChartMap_ι, Category.assoc]
    _ = (qX ⁻¹ᵁ (f₀ ⁻¹ᵁ U)).ι ≫ qX ≫ f₀ := by rw [h]
    _ = (qX ∣_ (f₀ ⁻¹ᵁ U) ≫ (f₀ ⁻¹ᵁ U).ι) ≫ f₀ := by
      rw [morphismRestrict_ι, Category.assoc]
    _ = (qX ∣_ (f₀ ⁻¹ᵁ U) ≫ f₀ ∣_ U) ≫ U.ι := by
      rw [Category.assoc, Category.assoc, morphismRestrict_ι]

private theorem ker_open_of_restrict_injective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] (U : Y.Opens) (hU : IsAffineOpen U)
    (h : Function.Injective (f ∣_ U).appTop.hom) :
    f.ker.ideal ⟨U, hU⟩ = ⊥ := by
  let : IsAffine U.toScheme := hU
  have hk : (f ∣_ U).ker.ideal ⟨⊤, isAffineOpen_top _⟩ = ⊥ := by
    rw [Scheme.Hom.ker_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp h
  have he := Scheme.ker_morphismRestrict_ideal f U ⟨⊤, isAffineOpen_top _⟩
  have heq : (⟨U.ι ''ᵁ ⊤, (isAffineOpen_top U.toScheme).image_of_isOpenImmersion U.ι⟩ :
      Y.affineOpens) = ⟨U, hU⟩ := Subtype.ext U.ι_image_top
  exact (congrArg (fun W : Y.affineOpens ↦ f.ker.ideal W = ⊥) heq).mp
    (he.symm.trans hk)

private theorem appTop_injective_of_comp {W X Y : Scheme.{u}}
    (t : W ⟶ X) (f : X ⟶ Y)
    (h : Function.Injective (t ≫ f).appTop.hom) :
    Function.Injective f.appTop.hom := by
  intro a b hab
  apply h
  rw [Scheme.Hom.comp_appTop]
  exact congrArg t.appTop.hom hab

/-- Retained arithmetic image kernels give zero kernel on the corresponding
affine open of every prescribed scalar endpoint. -/
theorem boundary_scalar_kernel_zero {S R K : Type u}
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
    (U : D.left.Opens) (hU : IsAffineOpen U)
    (V : (e.left ⁻¹ᵁ U).toScheme.OpenCover.{u}) [Finite V.I₀]
    (hV : ∀ j, IsAffine (V.X j))
    (hker : kernelExtensionData
      (Algebra.TensorProduct.lTensor (S := R) R (boundaryCoverMap C D e U V)))
    (hUK : IsAffineOpen (qY ⁻¹ᵁ U)) :
    f.left.ker.ideal ⟨qY ⁻¹ᵁ U, hUK⟩ = ⊥ := by
  let : IsAffine U.toScheme := hU
  let g := scalarChartMap e.left f.left qX qY hf U
  have hg : g ≫ ((qY ⁻¹ᵁ U).ι ≫ Y.hom) =
      (qX ⁻¹ᵁ (e.left ⁻¹ᵁ U)).ι ≫ X.hom := by
    rw [← Category.assoc, scalarChartMap_ι, Category.assoc, f.w]
  have he : e.left ∣_ U ≫ (U.ι ≫ D.hom) =
      (e.left ⁻¹ᵁ U).ι ≫ C.hom := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, e.w]
  have hi : Function.Injective g.appTop.hom :=
    chosen_cover_appTop_injective
      ((e.left ⁻¹ᵁ U).ι ≫ C.hom) (U.ι ≫ D.hom)
      ((qX ⁻¹ᵁ (e.left ⁻¹ᵁ U)).ι ≫ X.hom) ((qY ⁻¹ᵁ U).ι ≫ Y.hom)
      (e.left ∣_ U) g he hg (qX ∣_ (e.left ⁻¹ᵁ U)) (qY ∣_ U)
      ((isPullback_morphismRestrict qX _).paste_vert hX)
      ((isPullback_morphismRestrict qY _).paste_vert hY)
      (scalarChartMap_square e.left f.left qX qY hf U) V hV hker
  apply ker_open_of_restrict_injective f.left _ hUK
  exact appTop_injective_of_comp
    (eqToHom (congrArg Scheme.Opens.toScheme
      (endpoint_open_eq e.left f.left qX qY hf U).symm))
    (f.left ∣_ (qY ⁻¹ᵁ U)) hi

end SchubertGeometry
