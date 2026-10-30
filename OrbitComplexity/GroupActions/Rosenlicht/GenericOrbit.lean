import OrbitComplexity.GroupActions.Actions.OrbitMap
import OrbitComplexity.GroupActions.Rosenlicht.Invariants
import OrbitComplexity.GroupActions.Rosenlicht.InvariantRelations
import OrbitComplexity.GroupActions.Rosenlicht.FiniteTests

/-!
# Generic relations of algebraic group actions

Translation automorphisms of a variety induce actions on its rational functions.
The relations of any finite tuple of rational functions have finitely many
generators whose coefficients are invariant rational functions.

## Main definitions

* `Variety.invariantField`: rational functions invariant under point translations.
* `Variety.genericOrbitIdeal`: relations of every translate of a rational-function tuple.

## Main results

* `Variety.exists_invariant_relations`: the generic orbit ideal has finitely many
  generators with coefficients in the invariant field.
* `Variety.exists_finite_relation_tests`: finitely many point translations test
  every relation up to a fixed degree.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u w

variable {K : Type u} [Field K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [IrreducibleSpace X.scheme]

/-- The field of rational functions fixed by every rational point translation. -/
def invariantField :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    IntermediateField K X.scheme.functionField :=
  letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  invariantFunctionField K (translationHom H X)

/-- Polynomial relations vanishing at every point-translate of a tuple of rational functions. -/
def genericOrbitIdeal {ι : Type w} (x : ι → X.scheme.functionField) :
    Ideal (MvPolynomial ι X.scheme.functionField) :=
  letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  letI := functionFieldAction (schemeTranslationHom H X)
  orbitIdeal (G := H.points) x

/-- The generic orbit relations of a finite tuple have finitely many generators
whose coefficients belong to the invariant rational-function field. -/
theorem exists_invariant_relations {ι : Type w} [Finite ι]
    (x : ι → X.scheme.functionField) :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    ∃ s : Finset (MvPolynomial ι X.scheme.functionField),
      Ideal.span (s : Set (MvPolynomial ι X.scheme.functionField)) = genericOrbitIdeal H X x ∧
      ∀ p ∈ s, ∀ m : ι →₀ ℕ, p.coeff m ∈ invariantField H X := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let _ := functionFieldAction (schemeTranslationHom H X)
  obtain ⟨s, hs, hcoeff⟩ := exists_fixed_orbitIdeal_generators (G := H.points) x
  refine ⟨s, hs, ?_⟩
  intro p hp m
  change ∀ h : H.points,
    functionFieldMap ((schemeTranslationHom H X) h).inv (p.coeff m) = p.coeff m
  exact fun h ↦ hcoeff p hp h m

end

end GroupActions.Variety
