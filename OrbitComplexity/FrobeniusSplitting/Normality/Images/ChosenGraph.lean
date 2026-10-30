import OrbitComplexity.FrobeniusSplitting.Normality.GraphElements
import OrbitComplexity.FrobeniusSplitting.Normality.ModelComparison

/-! # Finite diagrams on prescribed algebra models -/

noncomputable section
namespace FrobeniusSplitting
open scoped TensorProduct
universe u v w z y

/-- Finite diagrams and elements descend on scalar extensions of the prescribed
presentation models. -/
theorem exists_chosen_graph_elements
    {K : Type u} [Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} {J : Type w} [Finite I] [Finite J]
    (M A : I → Type u) [∀ i, CommRing (M i)] [∀ i, Algebra S (M i)]
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    (e : ∀ i, K ⊗[S] M i ≃ₐ[K] A i)
    (vars rels : I → Type z) [∀ i, Finite (vars i)] [∀ i, Finite (rels i)]
    (Q : ∀ i, Algebra.Presentation S (M i) (vars i) (rels i))
    (src tgt : J → I) (f : ∀ b, A (src b) →ₐ[K] A (tgt b))
    (L : I → Type y) [∀ i, Finite (L i)] (a : ∀ i, L i → A i) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      ∃ f₀ : ∀ b, R ⊗[S] M (src b) →ₐ[R] R ⊗[S] M (tgt b),
        R.FG ∧
        (∀ b x, e (tgt b)
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
            (AlgHom.id S (M (tgt b))) (f₀ b x)) =
          f b (e (src b)
            (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
              (AlgHom.id S (M (src b))) x))) ∧
        ∀ i j, ∃ x : R ⊗[S] M i,
          e i (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
            (AlgHom.id S (M i)) x) = a i j := by
  classical
  let P i := ((Q i).baseChange K).ofAlgEquiv (e i)
  obtain ⟨R, hP, maps, hSR, hR, _, hcomm, helts⟩ :=
    exists_arithmetic_graph_elements S hS A vars rels P src tgt f L a
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  have (i : I) : IsScalarTower S R (A i) :=
    Subalgebra.inclusion.isScalarTower_right hSR (A i)
  have (i : I) : (P i).HasCoeffs R := hP i
  let E i := baseChangeModelEquivOf (Q i) (e i)
    (FaithfulSMul.algebraMap_injective R K)
  have hE i (x : (P i).ModelOfHasCoeffs R) :
      (P i).tensorModelOfHasCoeffsEquiv R ((1 : K) ⊗ₜ[R] x) =
      e i (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
        (AlgHom.id S (M i)) (E i x)) :=
    baseChangeModelEquiv_naturality (Q i) (e i)
      (FaithfulSMul.algebraMap_injective R K) x
  let f₀ b := (E (tgt b)).toAlgHom.comp
    ((maps b).comp (E (src b)).symm.toAlgHom)
  refine ⟨R, hSR, f₀, hR, ?_, ?_⟩
  · intro b x
    have h := DFunLike.congr_fun (hcomm b)
      ((1 : K) ⊗ₜ[R] (E (src b)).symm x)
    change (P (tgt b)).tensorModelOfHasCoeffsEquiv R
      ((1 : K) ⊗ₜ[R] maps b ((E (src b)).symm x)) =
      f b ((P (src b)).tensorModelOfHasCoeffsEquiv R
        ((1 : K) ⊗ₜ[R] (E (src b)).symm x)) at h
    rw [hE, hE, AlgEquiv.apply_symm_apply] at h
    exact h
  · intro i j
    obtain ⟨x, hx⟩ := helts i j
    exact ⟨E i x, (hE i x).symm.trans hx⟩


end FrobeniusSplitting
