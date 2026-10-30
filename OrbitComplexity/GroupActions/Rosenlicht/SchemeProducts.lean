import OrbitComplexity.GroupActions.Rosenlicht.AffineProducts
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Integral products with affine schemes

An integral affine scheme locally of finite type over an algebraically closed
field is geometrically integral. The statement is independent of a chosen
coordinate algebra, so it applies to an affine algebraic group as given.

## Main results

* `geometricallyIntegral_of_isAffine`: geometric integrality of an affine integral scheme.
* `isIntegral_pullback_of_isAffine`: integrality of products with an affine factor.
-/

namespace GroupActions

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- An integral affine scheme locally of finite type over an algebraically closed
field is geometrically integral over that field. -/
theorem geometricallyIntegral_of_isAffine {X : Scheme.{u}} [IsAffine X] [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] : GeometricallyIntegral f := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ f)
  have hft : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
  algebraize [φ.hom]
  have : Algebra.FiniteType K Γ(X, ⊤) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
    change (algebraMap K Γ(X, ⊤)).FiniteType at hft
    simpa only [RingHom.finiteType_algebraMap] using hft
  have hf : GeometricallyIntegral (X.isoSpec.inv ≫ f) := by
    rw [← hφ]
    exact geometricallyIntegral_affine
  constructor
  intro L _ y Z fst snd h
  apply hf.geometrically_isIntegral y (fst ≫ X.isoSpec.hom) snd
  exact h.of_iso (.refl Z) X.isoSpec (.refl _) (.refl _) (by simp) (by simp)
    (by simp) (by simp)

/-- The product of an integral affine scheme locally of finite type over an
algebraically closed field with an integral locally noetherian scheme is integral. -/
theorem isIntegral_pullback_of_isAffine {X Y : Scheme.{u}}
    [IsAffine X] [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    IsIntegral (pullback f g) := by
  have : GeometricallyIntegral f := geometricallyIntegral_of_isAffine f
  infer_instance

end

end GroupActions
