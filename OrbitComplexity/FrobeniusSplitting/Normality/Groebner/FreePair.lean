import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.FreeBaseChange
import Mathlib.RingTheory.TensorProduct.Maps

/-! One coefficient enlargement for two prescribed arithmetic algebra models. -/

open TensorProduct

namespace FrobeniusSplitting

variable {K A B : Type*} [Field K] [CommRing A] [CommRing B]

/-- Two finitely presented arithmetic models become free over one coefficient ring. -/
theorem exists_free_pair_models (S : Subalgebra ℤ K) (hS : S.FG)
    [Algebra S A] [Algebra S B]
    [Algebra.FinitePresentation S A] [Algebra.FinitePresentation S B] :
    ∃ R : Subalgebra ℤ K, R.FG ∧ ∃ hSR : S ≤ R,
      letI : Algebra S R := (Subalgebra.inclusion hSR).toRingHom.toAlgebra
      Module.Free R (R ⊗[S] A) ∧ Module.Free R (R ⊗[S] B) := by
  obtain ⟨R₁, hR₁, hS₁, hfree₁⟩ := exists_free_baseChange (B := A) S hS
  let : Algebra S R₁ := (Subalgebra.inclusion hS₁).toRingHom.toAlgebra
  have : Module.Free R₁ (R₁ ⊗[S] A) := hfree₁
  obtain ⟨R₂, hR₂, h₁₂, hfree₂⟩ :=
    exists_free_baseChange (B := R₁ ⊗[S] B) R₁ hR₁
  let : Algebra R₁ R₂ := (Subalgebra.inclusion h₁₂).toRingHom.toAlgebra
  have hS₂ : S ≤ R₂ := hS₁.trans h₁₂
  let : Algebra S R₂ := (Subalgebra.inclusion hS₂).toRingHom.toAlgebra
  have : IsScalarTower S R₁ R₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hA : Module.Free R₂ (R₂ ⊗[S] A) :=
    Module.Free.of_equiv
      (Algebra.TensorProduct.cancelBaseChange S R₁ R₂ R₂ A).toLinearEquiv
  have hB : Module.Free R₂ (R₂ ⊗[S] B) := by
    have : Module.Free R₂ (R₂ ⊗[R₁] (R₁ ⊗[S] B)) := hfree₂
    exact Module.Free.of_equiv
      (Algebra.TensorProduct.cancelBaseChange S R₁ R₂ R₂ B).toLinearEquiv
  exact ⟨R₂, hR₂, hS₂, hA, hB⟩

end FrobeniusSplitting
