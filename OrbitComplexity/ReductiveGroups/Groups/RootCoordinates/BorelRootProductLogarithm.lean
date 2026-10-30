import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.LogarithmCoordinateMap
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaSubgroupParameters

/-!
# Borel Root Product Logarithm

The original ordered Ga product followed by a linear logarithm
coordinate is a polynomial in the original Ga parameters. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

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

/-- Pull back an original logarithm coordinate along the ordered
Ga product. This is a polynomial, not an arbitrary pointwise function. -/
def borelRootProductLogarithm
    (x : κ → B →ₐc[K] SymmetricAlgebra K K) (l : List κ)
    (f : rootTangentSpace J π hπ →ₗ[K] K) : MvPolynomial κ K :=
  gaProductCoordinate x l (borelRootLogarithmCoordinate J hJ π hπ f)

/-- Evaluation is exactly the chosen linear form of the inverse tangent
of the same ordered product, with subgroup membership proved from its
Ga tangents. The list may be empty or contain repetitions. -/
theorem borelRootProductLogarithm_eval
    (x : κ → B →ₐc[K] SymmetricAlgebra K K)
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    (l : List κ) (f : rootTangentSpace J π hπ →ₗ[K] K) (a : κ → K) :
    MvPolynomial.aeval a (borelRootProductLogarithm J hJ π hπ x l f) =
      f ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm
        ⟨(l.map (fun i => gaParameterPoint (x i) (a i))).prod,
          GaParameterPoint.prod_mem_of_tangent_mem_quotient x
            (borelRootUnipotentHopfIdeal J π hπ) hx l a⟩) := by
  have hp := congrArg (fun φ : B →ₐ[K] K =>
    φ (borelRootLogarithmCoordinate J hJ π hπ f)) (gaProductCoordinate_eval x l a)
  simp only [AlgHom.comp_apply] at hp
  rw [borelRootProductLogarithm, hp]
  exact borelRootLogarithmCoordinate_eval J hJ π hπ f
    ⟨(l.map (fun i => gaParameterPoint (x i) (a i))).prod,
      GaParameterPoint.prod_mem_of_tangent_mem_quotient x
        (borelRootUnipotentHopfIdeal J π hπ) hx l a⟩

end ReductiveGroups
