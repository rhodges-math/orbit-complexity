import OrbitComplexity.FrobeniusSplitting.Normality.Lift
import OrbitComplexity.FrobeniusSplitting.Normality.Sections
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Dominant factorization through affine normalization

A normal integral source has global sections integrally closed in its function field.
The fraction-field embedding therefore lifts the normalization of an affine target
to these sections. The resulting scheme morphism factors the original map and is dominant.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u

/-- A dominant quasi-compact map from a normal integral scheme to an affine integral
scheme factors dominantly through its normalization. -/
theorem exists_normalizationLift {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of R))
    [QuasiCompact f] [IsDominant f]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ h : X ⟶ Spec (.of (integralClosure R (FractionRing R))),
      h ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (integralClosure R (FractionRing R)))) = f ∧ IsDominant h := by
  have : IsSchemeTheoreticallyDominant f := .of_isDominant _
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let C := integralClosure R (FractionRing R)
  let e := Scheme.ΓSpecIso (.of R)
  let φ : R →+* Γ(X, ⊤) := (e.inv ≫ f.appTop).hom
  let : Algebra R Γ(X, ⊤) := φ.toAlgebra
  let : Algebra R X.functionField := ((X.germToFunctionField ⊤).hom.comp φ).toAlgebra
  have : IsScalarTower R Γ(X, ⊤) X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  have hφ : Function.Injective φ := (f.app_injective ⊤).comp
    e.symm.commRingCatIsoToRingEquiv.injective
  have : FaithfulSMul R X.functionField :=
    (faithfulSMul_iff_algebraMap_injective R X.functionField).mpr
      ((X.germToFunctionField_injective ⊤).comp hφ)
  have : IsIntegrallyClosedIn Γ(X, ⊤) X.functionField :=
    isIntegrallyClosedIn_functionField hn
  let ℓ : C →ₐ[R] Γ(X, ⊤) := normalizationLift R Γ(X, ⊤) X.functionField
  let ψ := CommRingCat.ofHom ℓ.toRingHom
  let h : X ⟶ Spec (.of C) := ΓSpec.adjunction.homEquiv X (op (.of C)) ψ.op
  have happ : h.appTop = (Scheme.ΓSpecIso (.of C)).hom ≫ ψ :=
    ΓSpec_adjunction_homEquiv_eq ψ
  have hinj : Function.Injective h.appTop := by
    rw [happ]
    exact (normalizationLift_injective R Γ(X, ⊤) X.functionField).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of C)).hom).1
  have : IsDominant h := isDominant_of_of_appTop_injective hinj
  refine ⟨h, ?_, inferInstance⟩
  apply ext_to_Spec
  change e.inv ≫ (h ≫ Spec.map (CommRingCat.ofHom (algebraMap R C))).appTop =
    e.inv ≫ f.appTop
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc]
  rw [ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
  ext r
  exact ℓ.commutes r

end FrobeniusSplitting
