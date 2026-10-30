import OrbitComplexity.FrobeniusSplitting.Normality.ArithmeticFibres
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.FiniteStability

/-!
# Simultaneous arithmetic models

A finite family of finitely presented algebras has models over one finitely generated integer
subalgebra of the coefficient ring. For smooth algebras the models can also be chosen smooth:
first descend each algebra, then extend all models to a common coefficient ring.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- Finite families admit arithmetic models preserving smoothness on any selected objects. -/
theorem exists_models_smooth_on {I : Type*} [Finite I]
    {K : Type u} [CommRing K] (A : I → Type u) [∀ i, CommRing (A i)]
    [∀ i, Algebra K (A i)] [∀ i, Algebra.FinitePresentation K (A i)]
    (smoothNodes : Set I) (hsm : ∀ i ∈ smoothNodes, Algebra.Smooth K (A i)) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ ∀ i,
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B),
        Algebra.FinitePresentation R B ∧ (i ∈ smoothNodes → Algebra.Smooth R B) ∧
        Nonempty (K ⊗[R] B ≃ₐ[K] A i) := by
  classical
  have hdata (i : I) : ∃ (S : Subalgebra ℤ K) (B : Type u)
      (_ : CommRing B) (_ : Algebra S B), S.FG ∧ Algebra.FinitePresentation S B ∧
      (i ∈ smoothNodes → Algebra.Smooth S B) ∧ Nonempty (K ⊗[S] B ≃ₐ[K] A i) := by
    by_cases hi : i ∈ smoothNodes
    · have : Algebra.Smooth K (A i) := hsm i hi
      obtain ⟨S, B, _, _, hfg, hsmooth, e⟩ :=
        Algebra.Smooth.exists_subalgebra_fg ℤ K (A i)
      exact ⟨S, B, inferInstance, inferInstance, hfg, inferInstance,
        (fun _ ↦ hsmooth), ⟨e.some.symm⟩⟩
    · let P := Algebra.Presentation.ofFinitePresentation K (A i)
      let S := P.core
      have : P.HasCoeffs S := by
        constructor
        rw [Subalgebra.setRange_algebraMap]
        exact P.coeffs_subset_core
      exact ⟨S, P.ModelOfHasCoeffs S, inferInstance, inferInstance,
        Subalgebra.fg_def.mpr ⟨P.coeffs, P.finite_coeffs, rfl⟩, inferInstance,
        (fun h ↦ (hi h).elim), ⟨P.tensorModelOfHasCoeffsEquiv S⟩⟩
  choose Si B ringB algB fgB fpB smoothB e using hdata
  let (i : I) : CommRing (B i) := ringB i
  let (i : I) : Algebra (Si i) (B i) := algB i
  have (i : I) : Algebra.FinitePresentation (Si i) (B i) := fpB i
  choose s hs hgen using fun i ↦ Subalgebra.fg_def.mp (fgB i)
  let R : Subalgebra ℤ K := Algebra.adjoin ℤ (⋃ i, s i)
  have hfg : R.FG := Subalgebra.fg_def.mpr ⟨_, Set.finite_iUnion hs, rfl⟩
  have hle (i : I) : Si i ≤ R := by
    rw [← hgen i]
    exact Algebra.adjoin_mono (Set.subset_iUnion_of_subset i Set.Subset.rfl)
  refine ⟨R, hfg, fun i ↦ ?_⟩
  let : Algebra (Si i) R := (Subalgebra.inclusion (hle i)).toAlgebra
  have : IsScalarTower (Si i) R K := Subalgebra.inclusion.isScalarTower_right (hle i) K
  refine ⟨R ⊗[Si i] B i, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro hi
    have : Algebra.Smooth (Si i) (B i) := smoothB i hi
    infer_instance
  · exact ⟨(Algebra.TensorProduct.cancelBaseChange (Si i) R K K (B i)).trans (e i).some⟩

end FrobeniusSplitting
