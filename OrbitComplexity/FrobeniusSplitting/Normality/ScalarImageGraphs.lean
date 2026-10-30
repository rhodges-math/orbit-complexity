import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.PresentationGraphs
import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImages

/-!
# ScalarImageGraphs

Finite coefficient graphs retain their product comparisons.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- Finite graphs of chosen models descend to their intrinsic coefficient images,
with selected smooth objects and prescribed elements retained. -/
theorem exists_scalar_image_graph {I J : Type*} [Finite I] [Finite J]
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    (M A : I → Type u) [∀ i, CommRing (M i)] [∀ i, CommRing (A i)]
    [∀ i, Algebra S (M i)] [∀ i, Algebra K (A i)]
    [∀ i, Algebra.FinitePresentation S (M i)]
    (e : ∀ i, K ⊗[S] M i ≃ₐ[K] A i)
    (smoothNodes : Set I) (hsm : ∀ i ∈ smoothNodes, Algebra.Smooth S (M i))
    (src tgt : J → I) (f : ∀ b, A (src b) →ₐ[K] A (tgt b))
    (L : I → Type*) [∀ i, Finite (L i)] (a : ∀ i, L i → A i) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      ∃ (models : ∀ i, Subalgebra R (A i))
        (comparison : ∀ i, K ⊗[R] models i ≃ₐ[K] A i),
        R.FG ∧ (∀ i, models i = (scalarImageHom (R := R) (e i)).range) ∧
        (∀ i, Algebra.FinitePresentation R (models i)) ∧
        (∀ i, i ∈ smoothNodes → Algebra.Smooth R (models i)) ∧
        (∀ i (k : K) (m : models i),
          comparison i (k ⊗ₜ[R] m) = algebraMap K (A i) k * m.val) ∧
        (∀ b, Set.MapsTo (f b) (models (src b)) (models (tgt b))) ∧
        ∀ i j, a i j ∈ models i := by
  classical
  let vars (i : I) := Fin (Algebra.Presentation.ofFinitePresentationVars S (M i))
  let rels (i : I) := Fin (Algebra.Presentation.ofFinitePresentationRels S (M i))
  let Q (i : I) : Algebra.Presentation S (M i) (vars i) (rels i) :=
    Algebra.Presentation.ofFinitePresentation S (M i)
  obtain ⟨R, hP, models, comparison, hSR, hfg, hmodels, hfp, hsmooth,
    heval, hmaps, helts⟩ :=
    exists_presentation_image_graph S hS M A vars rels Q e
      smoothNodes hsm src tgt f L a
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  have : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  have (i : I) : (((Q i).baseChange K).ofAlgEquiv (e i)).HasCoeffs R := hP i
  refine ⟨R, hSR, models, comparison, hfg, ?_, hfp, hsmooth, heval, hmaps, helts⟩
  intro i
  rw [hmodels i]
  exact modelImage_eq_scalarImage (Q i) (e i) (FaithfulSMul.algebraMap_injective R K)

end FrobeniusSplitting
