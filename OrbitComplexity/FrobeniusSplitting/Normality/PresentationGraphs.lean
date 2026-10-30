import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.GraphElements
import OrbitComplexity.FrobeniusSplitting.Normality.ModelBaseChange
import OrbitComplexity.FrobeniusSplitting.Normality.ModelFlat

/-!
# Presentation Graphs

Presentation-model images retain graph maps, elements and selected smoothness.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- Chosen presentation images descend with graph maps, selected smooth objects and elements. -/
theorem exists_presentation_image_graph {I J : Type*} [Finite I] [Finite J]
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    (M A : I → Type u) [∀ i, CommRing (M i)] [∀ i, CommRing (A i)]
    [∀ i, Algebra S (M i)] [∀ i, Algebra K (A i)]
    (vars rels : I → Type*) [∀ i, Finite (vars i)] [∀ i, Finite (rels i)]
    (Q : ∀ i, Algebra.Presentation S (M i) (vars i) (rels i))
    (e : ∀ i, K ⊗[S] M i ≃ₐ[K] A i)
    (smoothNodes : Set I) (hsm : ∀ i ∈ smoothNodes, Algebra.Smooth S (M i))
    (src tgt : J → I) (f : ∀ a, A (src a) →ₐ[K] A (tgt a))
    (L : I → Type*) [∀ i, Finite (L i)] (a : ∀ i, L i → A i) :
    let P (i : I) := ((Q i).baseChange K).ofAlgEquiv (e i)
    ∃ (R : Subalgebra ℤ K) (_ : ∀ i, (P i).HasCoeffs R)
      (models : ∀ i, Subalgebra R (A i))
      (comparison : ∀ i, K ⊗[R] models i ≃ₐ[K] A i),
      S ≤ R ∧ R.FG ∧
      (∀ i, models i = (tensorImageHom ((P i).tensorModelOfHasCoeffsEquiv R)).range) ∧
      (∀ i, Algebra.FinitePresentation R (models i)) ∧
      (∀ i, i ∈ smoothNodes → Algebra.Smooth R (models i)) ∧
      (∀ i (k : K) (m : models i),
        comparison i (k ⊗ₜ[R] m) = algebraMap K (A i) k * (m : A i)) ∧
      (∀ b, Set.MapsTo (f b) (models (src b)) (models (tgt b))) ∧
      ∀ i j, a i j ∈ models i := by
  classical
  let P (i : I) := ((Q i).baseChange K).ofAlgEquiv (e i)
  obtain ⟨R, hP, maps, hSR, hfg, hfp, hcomm, hlift⟩ :=
    exists_arithmetic_graph_elements S hS A vars rels P src tgt f L a
  have : Algebra.FiniteType ℤ R := (Subalgebra.fg_iff_finiteType R).mp hfg
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  have : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  have (i : I) : (P i).HasCoeffs R := hP i
  have (i : I) : Algebra.FinitePresentation R ((P i).ModelOfHasCoeffs R) := hfp i
  let eP (i : I) := (P i).tensorModelOfHasCoeffsEquiv R
  let models (i : I) : Subalgebra R (A i) := (tensorImageHom (eP i)).range
  have hsmooth (i : I) (hi : i ∈ smoothNodes) : Algebra.Smooth R (models i) := by
    have : Algebra.Smooth S (M i) := hsm i hi
    have : Algebra.Smooth R ((P i).ModelOfHasCoeffs R) :=
      smooth_baseChangeModel (Q i) (e i) (FaithfulSMul.algebraMap_injective R K)
    exact tensorImage_smooth (eP i) (FaithfulSMul.algebraMap_injective R K)
  refine ⟨R, hP, models, (fun i ↦ tensorImageEquiv (eP i)), hSR, hfg,
    (fun _ ↦ rfl), (fun i ↦ tensorImage_finitePresentation (eP i)), hsmooth,
    (fun i k m ↦ tensorImageEquiv_tmul (eP i) k m), ?_, ?_⟩
  · intro b x hx
    obtain ⟨m, hm⟩ := hx
    change tensorImageHom (eP (src b)) m = x at hm
    refine ⟨maps b m, ?_⟩
    change tensorImageHom (eP (tgt b)) (maps b m) = f b x
    have hsquare := AlgHom.congr_fun (hcomm b) ((1 : K) ⊗ₜ[R] m)
    change tensorImageHom (eP (tgt b)) (maps b m) =
      f b (tensorImageHom (eP (src b)) m) at hsquare
    simpa only [hm] using hsquare
  · intro i j
    obtain ⟨m, hm⟩ := hlift i j
    exact ⟨m, hm⟩

end FrobeniusSplitting
