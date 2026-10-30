import OrbitComplexity.GroupActions.Varieties.AffineVariety
import OrbitComplexity.GroupActions.Rosenlicht.BaseFields
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Affine models of finitely generated fields

A finitely generated field extension is the fraction field of a finite-type
integral algebra. Its spectrum is an affine variety with the prescribed function
field, compatibly with the base field.

## Main definitions

* `fieldModelAlgebra`: a finite-type integral algebra inside the field extension.
* `fieldModel`: its affine variety.
* `fieldModelFieldEquiv`: the identification of its function field with the extension.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable (K E : Type u) [Field K] [Field E] [Algebra K E] [Algebra.EssFiniteType K E]

/-- A finite-type algebra whose fraction field is the given finitely generated field. -/
abbrev fieldModelAlgebra : Subalgebra K E := Algebra.EssFiniteType.subalgebra K E

/-- The chosen finite-type algebra has the prescribed field as its fraction field. -/
instance fieldModel_fractionRing : IsFractionRing (fieldModelAlgebra K E) E := by
  have hs : Algebra.EssFiniteType.submonoid K E =
      nonZeroDivisors (fieldModelAlgebra K E) := by
    ext a
    simp only [Algebra.EssFiniteType.submonoid, Submonoid.mem_comap,
      IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
    change (a : E) ≠ 0 ↔ a ≠ 0
    exact Subtype.val_injective.ne_iff (x := a) (y := 0)
  change IsLocalization (nonZeroDivisors (fieldModelAlgebra K E)) E
  rw [← hs]
  infer_instance

/-- The affine variety associated to a finitely generated field extension. -/
abbrev fieldModel : GroupActions.Variety K := affineVariety K (fieldModelAlgebra K E)

/-- The affine field model is integral. -/
instance fieldModel_integral : IsIntegral (fieldModel K E).scheme := by
  change IsIntegral (Spec (.of (fieldModelAlgebra K E)))
  infer_instance

private lemma spec_functionField_scalar (A : Type u) [CommRing A] [Algebra K A]
    [IsDomain A] (c : K) :
    letI : (Spec (.of A)).Over (Spec (.of K)) :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap K A))⟩
    algebraMap K (Spec (.of A)).functionField c =
      algebraMap A (Spec (.of A)).functionField (algebraMap K A c) := by
  let _ : (Spec (.of A)).Over (Spec (.of K)) :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap K A))⟩
  change ((Scheme.ΓSpecIso (.of K)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop ≫
    (Spec (.of A)).presheaf.germ ⊤ (genericPoint (Spec (.of A))) trivial) c = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rfl

/-- The function field of the affine model is the original field extension,
as an algebra over the base field. -/
def fieldModelFieldEquiv :
    letI : (fieldModel K E).scheme.Over (Spec (.of K)) := ⟨(fieldModel K E).toSpec⟩
    (fieldModel K E).scheme.functionField ≃ₐ[K] E := by
  let _ : (fieldModel K E).scheme.Over (Spec (.of K)) := ⟨(fieldModel K E).toSpec⟩
  let _ : (Spec (.of (fieldModelAlgebra K E))).Over (Spec (.of K)) :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap K (fieldModelAlgebra K E)))⟩
  change (Spec (.of (fieldModelAlgebra K E))).functionField ≃ₐ[K] E
  have : IsFractionRing (fieldModelAlgebra K E)
      (Spec (.of (fieldModelAlgebra K E))).functionField :=
    functionField_isFractionRing_of_affine (.of (fieldModelAlgebra K E))
  have : IsScalarTower K (fieldModelAlgebra K E)
      (Spec (.of (fieldModelAlgebra K E))).functionField :=
    .of_algebraMap_eq fun c ↦ spec_functionField_scalar K (fieldModelAlgebra K E) c
  exact (IsLocalization.algEquiv (nonZeroDivisors (fieldModelAlgebra K E))
    (Spec (.of (fieldModelAlgebra K E))).functionField E).restrictScalars K

end

end GroupActions
