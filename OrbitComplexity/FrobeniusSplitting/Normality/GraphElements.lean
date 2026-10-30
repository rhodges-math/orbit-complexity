import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ModelMaps

/-!
# Graph Elements

Finite algebra graphs descend together with chosen finite families of elements.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- A graph of chosen presentations descends over a prescribed ring with finitely many elements. -/
theorem exists_arithmetic_graph_elements {I J : Type*} [Finite I] [Finite J]
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    (A : I → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    (vars rels : I → Type*) [∀ i, Finite (vars i)] [∀ i, Finite (rels i)]
    (P : ∀ i, Algebra.Presentation K (A i) (vars i) (rels i))
    (src tgt : J → I) (f : ∀ a, A (src a) →ₐ[K] A (tgt a))
    (L : I → Type*) [∀ i, Finite (L i)] (a : ∀ i, L i → A i) :
    ∃ (R : Subalgebra ℤ K) (_ : ∀ i, (P i).HasCoeffs R)
      (f₀ : ∀ b, (P (src b)).ModelOfHasCoeffs R →ₐ[R] (P (tgt b)).ModelOfHasCoeffs R),
      S ≤ R ∧ R.FG ∧ (∀ i, Algebra.FinitePresentation R ((P i).ModelOfHasCoeffs R)) ∧
      (∀ b, ((P (tgt b)).tensorModelOfHasCoeffsEquiv R).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (f₀ b)) =
        (f b).comp ((P (src b)).tensorModelOfHasCoeffsEquiv R).toAlgHom) ∧
      ∀ i j, ∃ x : (P i).ModelOfHasCoeffs R,
        (P i).tensorModelOfHasCoeffsEquiv R ((1 : K) ⊗ₜ[R] x) = a i j := by
  classical
  choose v hv using fun i j ↦ (P i).aeval_val_surjective (a i j)
  let extra : Set K := ⋃ i, ⋃ j, ((v i j).coeffs : Set K)
  have hextra : extra.Finite := Set.finite_iUnion fun i ↦
    Set.finite_iUnion fun j ↦ (v i j).coeffs.finite_toSet
  let T : Subalgebra ℤ K := S ⊔ Algebra.adjoin ℤ extra
  have hT : T.FG := hS.sup (Subalgebra.fg_def.mpr ⟨extra, hextra, rfl⟩)
  obtain ⟨R, hP, maps, hTR, hfg, hfp, hcomm⟩ :=
    exists_arithmetic_graph_over A vars rels P src tgt f T hT
  have hSR : S ≤ R := (show S ≤ T from le_sup_left).trans hTR
  have (i : I) : (P i).HasCoeffs R := hP i
  refine ⟨R, hP, maps, hSR, hfg, hfp, hcomm, ?_⟩
  intro i j
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : MvPolynomial (vars i) R,
      MvPolynomial.map (algebraMap R K) v₀ = v i j := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    refine ⟨⟨c, hTR ?_⟩, rfl⟩
    exact (show Algebra.adjoin ℤ extra ≤ T from le_sup_right)
      (Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hc⟩⟩))
  refine ⟨Ideal.Quotient.mk _ v₀, ?_⟩
  rw [Algebra.Presentation.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul,
    ← MvPolynomial.aeval_map_algebraMap K, hv₀]
  exact hv i j

end FrobeniusSplitting
