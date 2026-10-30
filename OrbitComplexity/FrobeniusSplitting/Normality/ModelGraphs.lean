import OrbitComplexity.FrobeniusSplitting.Normality.ModelFlat
import OrbitComplexity.FrobeniusSplitting.Normality.FiniteModels

/-!
# Arithmetic models of graphs with smooth objects

Finite graphs admit finitely presented subalgebra models over one integer coefficient ring.
A selected collection of smooth objects remains smooth after descending the graph morphisms.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

private theorem tensorImage_baseChange_one {S R K M A : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (e : K ⊗[S] M ≃ₐ[K] A) (m : M) :
    tensorImageHom ((Algebra.TensorProduct.cancelBaseChange S R K K M).trans e)
      ((1 : R) ⊗ₜ[S] m) = e ((1 : K) ⊗ₜ[S] m) := by
  rw [tensorImageHom_apply, AlgEquiv.trans_apply, Algebra.TensorProduct.cancelBaseChange_tmul]
  simp only [one_smul]

universe u

/-- A finite graph admits finitely presented arithmetic subalgebras preserving smoothness
on selected objects and preserved by every graph morphism. -/
theorem exists_arithmetic_graph_smooth_on {I J : Type*} [Finite I] [Finite J]
    {K : Type u} [CommRing K] (A : I → Type u) [∀ i, CommRing (A i)]
    [∀ i, Algebra K (A i)] [∀ i, Algebra.FinitePresentation K (A i)]
    (smoothNodes : Set I) (hsm : ∀ i ∈ smoothNodes, Algebra.Smooth K (A i))
    (src tgt : J → I) (f : ∀ a, A (src a) →ₐ[K] A (tgt a)) :
    ∃ R : Subalgebra ℤ K, R.FG ∧
      ∃ (models : ∀ i, Subalgebra R (A i))
        (e : ∀ i, K ⊗[R] models i ≃ₐ[K] A i),
        (∀ i, Algebra.FinitePresentation R (models i)) ∧
        (∀ i, i ∈ smoothNodes → Algebra.Smooth R (models i)) ∧
        (∀ i (k : K) (a : models i), e i (k ⊗ₜ[R] a) = algebraMap K (A i) k * (a : A i)) ∧
        ∀ a, Set.MapsTo (f a) (models (src a)) (models (tgt a)) := by
  classical
  obtain ⟨S, hS, hmodels⟩ := exists_models_smooth_on (K := K) A smoothNodes hsm
  choose M ringM algM fpM smoothM comparison using hmodels
  let (i : I) : CommRing (M i) := ringM i
  let (i : I) : Algebra S (M i) := algM i
  have (i : I) : Algebra.FinitePresentation S (M i) := fpM i
  let e (i : I) := (comparison i).some
  let vars (i : I) := Fin (Algebra.Presentation.ofFinitePresentationVars S (M i))
  let rels (i : I) := Fin (Algebra.Presentation.ofFinitePresentationRels S (M i))
  let Q (i : I) : Algebra.Presentation S (M i) (vars i) (rels i) :=
    Algebra.Presentation.ofFinitePresentation S (M i)
  let P (i : I) : Algebra.Presentation K (A i) (vars i) (rels i) :=
    ((Q i).baseChange K).ofAlgEquiv (e i)
  obtain ⟨R, hP, f₀, hSR, hfg, hfp, hcomm⟩ :=
    exists_arithmetic_graph_over A vars rels P src tgt f S hS
  have : Algebra.FiniteType ℤ R := (Subalgebra.fg_iff_finiteType R).mp hfg
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have (i : I) : Algebra.FinitePresentation R ((P i).ModelOfHasCoeffs R) := hfp i
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  have : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  have (i : I) : IsScalarTower S R (A i) :=
    Subalgebra.inclusion.isScalarTower_right hSR (A i)
  let eR (i : I) := (Algebra.TensorProduct.cancelBaseChange S R K K (M i)).trans (e i)
  let eP (i : I) := (P i).tensorModelOfHasCoeffsEquiv R
  let models (i : I) : Subalgebra R (A i) := (tensorImageHom (eP i)).range
  have hrange (i : I) : models i = (tensorImageHom (eR i)).range := by
    change (tensorImageHom ((P i).tensorModelOfHasCoeffsEquiv R)).range = _
    rw [tensorImageHom_range,
      tensorImage_range_of_generators ((Q i).baseChange R).toGenerators]
    apply congrArg (Algebra.adjoin R)
    apply congrArg Set.range
    funext j
    change e i ((1 : K) ⊗ₜ[S] (Q i).val j) =
      tensorImageHom (eR i) ((1 : R) ⊗ₜ[S] (Q i).val j)
    exact (tensorImage_baseChange_one (e i) ((Q i).val j)).symm
  have hsmooth (i : I) (hi : i ∈ smoothNodes) : Algebra.Smooth R (models i) := by
    have : Algebra.Smooth S (M i) := smoothM i hi
    rw [hrange i]
    exact tensorImage_smooth (eR i) (FaithfulSMul.algebraMap_injective R K)
  refine ⟨R, hfg, models, (fun i ↦ tensorImageEquiv (eP i)),
    (fun i ↦ tensorImage_finitePresentation (eP i)), hsmooth,
    (fun i k a ↦ tensorImageEquiv_tmul (eP i) k a), ?_⟩
  intro a x hx
  obtain ⟨m, hm⟩ := hx
  change tensorImageHom (eP (src a)) m = x at hm
  refine ⟨f₀ a m, ?_⟩
  change tensorImageHom (eP (tgt a)) (f₀ a m) = f a x
  have hsquare := AlgHom.congr_fun (hcomm a) ((1 : K) ⊗ₜ[R] m)
  change tensorImageHom (eP (tgt a)) (f₀ a m) =
    f a (tensorImageHom (eP (src a)) m) at hsquare
  simpa only [hm] using hsquare

end FrobeniusSplitting
