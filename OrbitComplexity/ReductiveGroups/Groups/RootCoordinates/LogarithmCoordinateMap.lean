import OrbitComplexity.ReductiveGroups.Groups.Representations.LogarithmCoordinates
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Logarithm Coordinate Map

Every linear coordinate of the inverse tangent is a regular
function on the original subgroup. These functions give a
coordinate-ring map for any family of tangent linear forms. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]
  {κ : Type v}

variable (J : HopfIdeal K B)
  (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
  (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
  (hπ : Function.Surjective π)

private abbrev rootTangentSpace (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) := (derivationCompLieHom (B := K)
  (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ)).hom).range

/-- A faithful matrix differential and a linear retraction express every
linear form on the subgroup tangent as an original coordinate
function evaluated on the inverse exponential. -/
theorem exists_borelRootLogarithmCoordinate (f : rootTangentSpace J π hπ →ₗ[K] K) :
    ∃ b : B, ∀ g : CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K),
      g.val.ofConv b = f ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm g) := by
  obtain ⟨n, ρ, _, hρ⟩ :=
    FiniteTypeAffineGroup.exists_injective_matrixDifferential (K := K) (B := B)
  let D : rootTangentSpace J π hπ →ₗ[K] Matrix (Fin n) (Fin n) K :=
    (affineGroupMatrixDifferential n ρ).toLinearMap.comp
      (derivationCompLieHom (B := K)
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
          (borelRootUnipotentHopfIdeal J π hπ)).hom).range.incl.toLinearMap
  have hD : LinearMap.ker D = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    exact hρ.comp Subtype.val_injective
  refine ⟨affineGroupLogarithmLinearCoordinate n ρ (f.comp D.leftInverse), ?_⟩
  intro g
  rw [BorelRootExponentialInverse.linearCoordinate J hJ π hπ g]
  change f (D.leftInverse (D _)) = _
  rw [LinearMap.leftInverse_apply_of_inj hD]

/-- A chosen original coordinate function representing the given linear
form of the inverse tangent on U(K). -/
def borelRootLogarithmCoordinate (f : rootTangentSpace J π hπ →ₗ[K] K) : B :=
  Classical.choose (exists_borelRootLogarithmCoordinate J hJ π hπ f)

/-- The equality is

```lean
g.val.ofConv (borelRootLogarithmCoordinate J hJ π hπ f) =
      f ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm g)
```
-/
theorem borelRootLogarithmCoordinate_eval (f : rootTangentSpace J π hπ →ₗ[K] K)
    (g : CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K)) :
    g.val.ofConv (borelRootLogarithmCoordinate J hJ π hπ f) =
      f ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm g) :=
  Classical.choose_spec (exists_borelRootLogarithmCoordinate J hJ π hπ f) g

/-- The coordinate pullback for any family of inverse-tangent linear
coordinates. Its restriction to the subgroup is obtained by the original
coordinate quotient. -/
def borelRootLogarithmCoordinateMap (f : κ → rootTangentSpace J π hπ →ₗ[K] K) :
    MvPolynomial κ K →ₐ[K] B :=
  MvPolynomial.aeval (fun i => borelRootLogarithmCoordinate J hJ π hπ (f i))

/-- Specializing the coordinate map agrees with applying the
given linear forms to the original inverse exponential. -/
theorem borelRootLogarithmCoordinateMap_eval (f : κ → rootTangentSpace J π hπ →ₗ[K] K)
    (g : CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K)) :
    g.val.ofConv.comp (borelRootLogarithmCoordinateMap J hJ π hπ f) =
      MvPolynomial.aeval
        (fun i => f i ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm g)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, borelRootLogarithmCoordinateMap, MvPolynomial.aeval_X]
  exact borelRootLogarithmCoordinate_eval J hJ π hπ (f i) g

end ReductiveGroups
