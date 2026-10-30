import OrbitComplexity.GroupActions.Varieties.AffinePoints
import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# AffineSchemePoints
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

private abbrev affineCoordinateAlgebra (R : CommRingCat.{u}) (Y : Scheme.{u})
    [Y.Over (Spec R)] [IsAffine Y] : Algebra R Γ(Y, ⊤) := inferInstance

variable (K : Type u) [CommRing K] (Y : Scheme.{u})
variable [Y.Over (Spec (.of K))] [IsAffine Y]

/-- Rational sections of an affine scheme correspond to algebra homomorphisms
from its global coordinate ring into the base ring. -/
def affineSchemePointsEquiv :
    letI : Algebra K Γ(Y, ⊤) := affineCoordinateAlgebra (.of K) Y
    {p : Spec (.of K) ⟶ Y // p ≫ (Y ↘ Spec (.of K)) = 𝟙 _} ≃
      (Γ(Y, ⊤) →ₐ[K] K) := by
  let : Algebra K Γ(Y, ⊤) := affineCoordinateAlgebra (.of K) Y
  let e : {p : Spec (.of K) ⟶ Y // p ≫ (Y ↘ Spec (.of K)) = 𝟙 _} ≃
      {p : Spec (.of K) ⟶ Spec Γ(Y, ⊤) //
        p ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(Y, ⊤))) = 𝟙 _} :=
    { toFun := fun p ↦ ⟨p.val ≫ Y.isoSpec.hom, by
        change (p.val ≫ Y.isoSpec.hom) ≫ (Spec Γ(Y, ⊤) ↘ Spec (.of K)) = _
        rw [Category.assoc, comp_over, p.property]⟩
      invFun := fun p ↦ ⟨p.val ≫ Y.isoSpec.inv, by
        rw [Category.assoc, comp_over]
        exact p.property⟩
      left_inv := fun p ↦ by
        apply Subtype.ext
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      right_inv := fun p ↦ by
        apply Subtype.ext
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] }
  exact e.trans affinePointsEquiv.symm

/-- The coordinate homomorphism of a rational section induces its composite
with the canonical affine-spectrum isomorphism. -/
theorem affineSchemePointsEquiv_spec
    (p : {p : Spec (.of K) ⟶ Y // p ≫ (Y ↘ Spec (.of K)) = 𝟙 _}) :
    letI : Algebra K Γ(Y, ⊤) := affineCoordinateAlgebra (.of K) Y
    Spec.map (CommRingCat.ofHom ((affineSchemePointsEquiv K Y) p).toRingHom) =
      p.val ≫ Y.isoSpec.hom := by
  let : Algebra K Γ(Y, ⊤) := affineCoordinateAlgebra (.of K) Y
  exact congrArg Subtype.val (affinePointsEquiv.apply_symm_apply
    ⟨p.val ≫ Y.isoSpec.hom, by
      change (p.val ≫ Y.isoSpec.hom) ≫ (Spec Γ(Y, ⊤) ↘ Spec (.of K)) = _
      rw [Category.assoc, comp_over, p.property]⟩)

/-- The coordinate homomorphism of a rational section evaluates a global
section by pullback to the spectrum of the base ring. -/
theorem affineSchemePointsEquiv_apply
    (p : {p : Spec (.of K) ⟶ Y // p ≫ (Y ↘ Spec (.of K)) = 𝟙 _})
    (a : Γ(Y, ⊤)) :
    letI : Algebra K Γ(Y, ⊤) := affineCoordinateAlgebra (.of K) Y
    ((affineSchemePointsEquiv K Y) p) a =
      (Scheme.ΓSpecIso (.of K)).hom (p.val.appTop a) := by
  let : Algebra K Γ(Y, ⊤) := affineCoordinateAlgebra (.of K) Y
  have he : CommRingCat.ofHom ((affineSchemePointsEquiv K Y) p).toRingHom =
      p.val.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom := by
    apply Spec.map_injective
    rw [affineSchemePointsEquiv_spec, Spec.map_comp, SpecMap_ΓSpecIso_hom,
      ← Scheme.toSpecΓ_naturality]
    rfl
  exact congrArg (fun f : Γ(Y, ⊤) ⟶ CommRingCat.of K ↦ f a) he

end

end GroupActions
