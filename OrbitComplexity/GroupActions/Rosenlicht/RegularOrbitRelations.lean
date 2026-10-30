import OrbitComplexity.GroupActions.Rosenlicht.PolynomialCharts
import OrbitComplexity.GroupActions.Rosenlicht.GenericOrbit

/-!
# Regular invariant generators of generic orbit ideals
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u v

variable {K : Type u} [Field K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [IrreducibleSpace X.scheme]

/-- The generic orbit ideal has generators with invariant rational coefficients
that are regular together on one affine neighborhood of the generic point. -/
theorem exists_regular_orbitRelations {ι : Type v} [Finite ι]
    (x : ι → X.scheme.functionField) :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    ∃ U : X.scheme.Opens, IsAffineOpen U ∧ ∃ hU : genericPoint X.scheme ∈ U,
      ∃ s : Finset (MvPolynomial ι Γ(X.scheme, U)),
        (Ideal.span (s : Set (MvPolynomial ι Γ(X.scheme, U)))).map
          (MvPolynomial.map (X.scheme.presheaf.germ U (genericPoint X.scheme) hU).hom) =
            genericOrbitIdeal H X x ∧
        ∀ p ∈ s, ∀ m : ι →₀ ℕ,
          X.scheme.presheaf.germ U (genericPoint X.scheme) hU (p.coeff m) ∈ invariantField H X := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  obtain ⟨P, hP, hcoeff⟩ := exists_invariant_relations H X x
  obtain ⟨U, hUa, hU, s, hs⟩ := exists_affine_polynomialChart X.scheme P
  refine ⟨U, hUa, hU, s, ?_, ?_⟩
  · rw [Ideal.map_span, hs]
    exact hP
  · intro p hp m
    have hmem : MvPolynomial.map
        (X.scheme.presheaf.germ U (genericPoint X.scheme) hU).hom p ∈ P :=
      by
        change _ ∈ (P : Set (MvPolynomial ι X.scheme.functionField))
        rw [← hs]
        exact ⟨p, hp, rfl⟩
    have h := hcoeff _ hmem m
    simpa only [MvPolynomial.coeff_map] using h

end

end GroupActions.Variety
