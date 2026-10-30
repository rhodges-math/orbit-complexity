import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImages
import Mathlib.RingTheory.Flat.Basic

/-! # Specification of the flat scalar-image comparison -/

open scoped TensorProduct
noncomputable section
namespace FrobeniusSplitting

/-- Flat scalar-image models identify with the chosen coefficient base change. -/
def scalarImageBaseChangeSpec {S R K M A : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (e : K ⊗[S] M ≃ₐ[K] A) : Prop :=
  ∃ d : R ⊗[S] M ≃ₐ[R] (scalarImageHom (R := R) e).range,
    ∀ z, (d z).val = scalarImageHom (R := R) e z

end FrobeniusSplitting
