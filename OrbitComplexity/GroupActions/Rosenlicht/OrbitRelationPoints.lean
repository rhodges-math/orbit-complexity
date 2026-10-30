import OrbitComplexity.GroupActions.Rosenlicht.AffineRelationFields
import OrbitComplexity.GroupActions.Rosenlicht.RegularOrbitRelations
import OrbitComplexity.GroupActions.Rosenlicht.RelationPoints
import OrbitComplexity.GroupActions.Varieties.Noetherian

/-!
# Invariant tests for ordinary orbit-relation points
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]
variable (V : X.scheme.Opens) [Nonempty V]

/-- On one affine first-coordinate chart, finitely many invariant regular
relations test the full relation-chart ideal at every point away from one
nonzero denominator. -/
theorem exists_orbitRelation_tests (m : ℕ) (c : Fin m → Γ(X.scheme, V)) :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    ∃ U : X.scheme.Opens, IsAffineOpen U ∧ ∃ hU : genericPoint X.scheme ∈ U,
      letI : Nonempty U := ⟨⟨genericPoint X.scheme, hU⟩⟩
      letI := relationChartAlgebra H X U V
      ∃ s : Finset (MvPolynomial (Fin m) Γ(X.scheme, U)), ∃ d : Γ(X.scheme, U),
        d ≠ 0 ∧
        (∀ p ∈ s, ∀ n : Fin m →₀ ℕ,
          X.scheme.germToFunctionField U (p.coeff n) ∈ invariantField H X) ∧
        ∀ (C : Type v) [CommRing C] (x : Γ(X.scheme, U) →+* C),
          IsUnit (x d) → ∀ y : Fin m → C,
            (∀ p ∈ RingHom.ker (relationChartCoordinates H X U V c),
              MvPolynomial.eval₂Hom x y p = 0) ↔
                ∀ p ∈ s, MvPolynomial.eval₂Hom x y p = 0 := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let z : Fin m → X.scheme.functionField := fun i ↦ X.scheme.germToFunctionField V (c i)
  obtain ⟨U, hUa, hU, s, hs, hcoeff⟩ := exists_regular_orbitRelations H X z
  have : Nonempty U := ⟨⟨genericPoint X.scheme, hU⟩⟩
  let := relationChartAlgebra H X U V
  let R := Γ(X.scheme, U)
  let F := X.scheme.functionField
  let f := relationChartCoordinates H X U V c
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hUa⟩
  have : IsDomain R := Function.Injective.isDomain
    (X.scheme.germToFunctionField U).hom (X.scheme.germToFunctionField_injective U)
  have : IsFractionRing R F := functionField_isFractionRing_of_isAffineOpen X.scheme U hUa
  have hgen : (RingHom.ker f).map (MvPolynomial.map (algebraMap R F)) =
      (Ideal.span (s : Set (MvPolynomial (Fin m) R))).map
        (MvPolynomial.map (algebraMap R F)) := by
    change (RingHom.ker (relationChartCoordinates H X U V c)).map
      (MvPolynomial.map (X.scheme.germToFunctionField U).hom) = _
    rw [relationChart_kernel H X U V hUa]
    exact hs.symm
  obtain ⟨d, hd, hpoint⟩ := exists_relation_vanishing R F m (RingHom.ker f) s hgen
  exact ⟨U, hUa, hU, s, d, hd, hcoeff, hpoint⟩

end

end GroupActions.Variety
