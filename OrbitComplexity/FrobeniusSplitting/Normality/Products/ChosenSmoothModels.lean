import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImageGraphs
import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImageProperties

/-! # Smoothness of a chosen coefficient model

Two presentations of the same algebra can be retained with identity maps in
both directions. Their coefficient images then agree, so smoothness of one
model transfers to the specified flat model after extending coefficients.
-/

open scoped TensorProduct
namespace FrobeniusSplitting
noncomputable section
universe u

/-- A specified flat model becomes smooth after extending coefficients when the
same generic algebra has a smooth model over the initial coefficient ring. -/
theorem exists_smooth_chosen_basechange {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) (M N A : Type u)
    [CommRing M] [CommRing N] [CommRing A]
    [Algebra S M] [Algebra S N] [Algebra K A]
    [Algebra.FinitePresentation S M] [Module.Flat S M] [Algebra.Smooth S N]
    (eM : K ⊗[S] M ≃ₐ[K] A) (eN : K ⊗[S] N ≃ₐ[K] A) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      R.FG ∧ Algebra.Smooth R (R ⊗[S] M) := by
  classical
  let initial : Bool → Type u
    | false => M
    | true => N
  let (b : Bool) : CommRing (initial b) := by
    cases b <;> dsimp only [initial] <;> infer_instance
  let (b : Bool) : Algebra S (initial b) := by
    cases b <;> dsimp only [initial] <;> infer_instance
  have (b : Bool) : Algebra.FinitePresentation S (initial b) := by
    cases b <;> dsimp only [initial] <;> infer_instance
  let comparison : ∀ b, K ⊗[S] initial b ≃ₐ[K] A
    | false => eM
    | true => eN
  have hsmooth : ∀ b ∈ ({true} : Set Bool), Algebra.Smooth S (initial b) := by
    intro b hb
    have heq : b = true := hb
    subst b
    exact inferInstanceAs (Algebra.Smooth S N)
  obtain ⟨R, hSR, models, e, hR, hmodels, hfp, hsm, heval, hmaps, helts⟩ :=
    exists_scalar_image_graph S hS initial (fun _ : Bool => A) comparison
      {true} hsmooth id Bool.not (fun _ => AlgHom.id K A)
      (fun _ => Empty) (fun _ z => nomatch z)
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  have : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  have heq : models false = models true := by
    apply le_antisymm
    · intro a ha
      exact hmaps false ha
    · intro a ha
      exact hmaps true ha
  have hfalse : Algebra.Smooth R (models false) := by
    rw [heq]
    exact hsm true (Set.mem_singleton true)
  have hrange : models false = (scalarImageHom (R := R) eM).range := hmodels false
  have : Algebra.Smooth R (scalarImageHom (R := R) eM).range := by
    rw [← hrange]
    exact hfalse
  let q : R ⊗[S] M →ₐ[R] A := scalarImageHom eM
  let E : R ⊗[S] M ≃ₐ[R] q.range := AlgEquiv.ofInjective q
    (scalarImageHom_injective eM (FaithfulSMul.algebraMap_injective R K))
  exact ⟨R, hSR, hR, Algebra.Smooth.of_equiv E.symm⟩

end
end FrobeniusSplitting
