import OrbitComplexity.FrobeniusSplitting.Normality.Products.PointedProductModels
import OrbitComplexity.FrobeniusSplitting.Normality.Products.ProductNormalFibres

/-! # Field fibres of pointed affine product models

The retained algebra-valued point defines a section of spectra.
The pointed smooth-product criterion then gives normal domain stalks on every
field fibre of the specified affine factor.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FrobeniusSplitting
noncomputable section
universe u

/-- Smooth affine factors and a retained point yield normal domain stalks on
every field fibre through the smooth product and its unit section. -/
theorem pointed_affine_fibre_stalks (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.Smooth R A] [Algebra.Smooth R B] (eps : B →ₐ[R] R)
    (L : Type u) [Field L] (f : R →+* L) :
    ∀ z : (pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom f)) : Scheme.{u}),
      IsDomain ((pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom f)) : Scheme.{u}).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom f)) : Scheme.{u}).presheaf.stalk z) := by
  let H : Over (Spec (CommRingCat.of R)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))
  let Z : Over (Spec (CommRingCat.of R)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  let e : Spec (CommRingCat.of R) ⟶ H.left :=
    Spec.map (CommRingCat.ofHom eps.toRingHom)
  have he : e ≫ H.hom = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom eps.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B)) = _
    rw [← Spec.map_comp]
    have h : CommRingCat.ofHom (algebraMap R B) ≫
        CommRingCat.ofHom eps.toRingHom = 𝟙 (CommRingCat.of R) := by
      ext r
      exact eps.commutes r
    rw [h, Spec.map_id]
  have : Smooth H.hom :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  have : Smooth Z.hom :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  have : Smooth (H ⊗ Z).hom := by
    change Smooth (pullback.fst H.hom Z.hom ≫ H.hom)
    infer_instance
  exact stalks_fibres_of_smooth_product H Z e he L (Spec.map (CommRingCat.ofHom f))

end
end FrobeniusSplitting
