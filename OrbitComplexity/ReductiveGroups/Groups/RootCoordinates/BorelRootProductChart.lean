import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductLinearCoefficients
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaSubgroupParameters
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootProductLogarithm

/-!
# Borel Root Product Chart

A conditional polynomial chart on the quotient coordinate ring
of the original Borel's Ga-only closed subgroup. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u v
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]
  {κ : Type v}

local notation "M" => Multiplicative (ι →₀ ℤ)

private abbrev rootTangentSpace (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) := (derivationCompLieHom (B := K)
  (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ)).hom).range

/-- The original ordered Ga product factors through the original Ga-only
closed subgroup coordinate quotient over the full polynomial value algebra. -/
def borelRootProductQuotientCoordinate
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π)
    (x : κ → B →ₐc[K] SymmetricAlgebra K K)
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    (l : List κ) :
    (B ⧸ (borelRootUnipotentHopfIdeal J π hπ).toIdeal) →ₐ[K]
      MvPolynomial κ K := by
  let H := CommHopfAlgCat.of K B
  let U := borelRootUnipotentHopfIdeal J π hπ
  let q := (CommHopfAlgCat.mkQuotient H U).hom.toAlgHom
  have hq : Function.Surjective q := CommHopfAlgCat.mkQuotient_surjective H U
  have hker : ∀ b : B, q b = 0 → gaProductCoordinate x l b = 0 := by
    intro b hb
    have hmem : b ∈ U := (CommHopfAlgCat.mkQuotient_eq_zero_iff H U b).mp hb
    have hp := GaParameterPoint.prod_mem_of_tangent_mem_quotient x U hx l
      (a := fun i => (MvPolynomial.X i : MvPolynomial κ K))
    exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff H U _ _).mp hp b hmem
  exact AlgHom.liftOfSurjective q hq (gaProductCoordinate x l) hker

/-- The equality is

```lean
(borelRootProductQuotientCoordinate J π hπ x hx l).comp
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom.toAlgHom =
      gaProductCoordinate x l
```
-/
theorem BorelRootProductQuotientCoordinate.comp_quotient
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π)
    (x : κ → B →ₐc[K] SymmetricAlgebra K K)
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    (l : List κ) :
    (borelRootProductQuotientCoordinate J π hπ x hx l).comp
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom.toAlgHom =
      gaProductCoordinate x l := by
  exact AlgHom.liftOfSurjective_comp _ _ _ _

/-- A polynomial automorphism whose generator images are exactly the
logarithm of the ordered product provides a right inverse to the
original quotient coordinate map. -/
theorem BorelRootProductQuotientCoordinate.comp_logarithm
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (x : κ → B →ₐc[K] SymmetricAlgebra K K)
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    (l : List κ) (e : Module.Basis κ K (rootTangentSpace J π hπ))
    (F : MvPolynomial κ K ≃ₐ[K] MvPolynomial κ K)
    (hF : ∀ i, F (MvPolynomial.X i) =
      borelRootProductLogarithm J hJ π hπ x l (e.coord i)) :
    (borelRootProductQuotientCoordinate J π hπ x hx l).comp
      ((CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom.toAlgHom.comp
        (borelRootLogarithmCoordinateMap J hJ π hπ e.coord)) = F.toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  change ((borelRootProductQuotientCoordinate J π hπ x hx l).comp
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ)).hom.toAlgHom)
        ((borelRootLogarithmCoordinateMap J hJ π hπ e.coord) (MvPolynomial.X i)) = _
  rw [BorelRootProductQuotientCoordinate.comp_quotient]
  change gaProductCoordinate x l
    (borelRootLogarithmCoordinateMap J hJ π hπ e.coord (MvPolynomial.X i)) =
      F (MvPolynomial.X i)
  rw [borelRootLogarithmCoordinateMap, MvPolynomial.aeval_X]
  exact (hF i).symm

end ReductiveGroups
