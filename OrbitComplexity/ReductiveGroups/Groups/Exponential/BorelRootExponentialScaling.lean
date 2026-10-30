import OrbitComplexity.ReductiveGroups.Groups.Exponential.BorelRootExponentialAdditivity

/-!
# Borel Root Exponential Scaling

Scalar reparametrization of the Borel root exponential. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)

omit [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B] in
private theorem faithful_point_matrixMap_injective (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ) :
    Function.Injective (fun p : WithConv (B →ₐ[K] K) =>
      GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ p)) := by
  intro p q hpq
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro b
  obtain ⟨a, rfl⟩ := hρ b
  have h := (GeneralLinear.pointsMulEquiv n).injective hpq
  have h' := congrArg (fun z : WithConv
    (GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] K) => z.ofConv a) h
  simpa only [AlgHom.mapDomain_apply_apply] using h'

/-- The exponential at a scalar multiple is exactly the corresponding point
of the unique Ga integration of the original subgroup tangent. -/
theorem borelRootUnipotentExponential_smul
    (J : HopfIdeal K B)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (d : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range)
    (t : K) :
    borelRootUnipotentExponential J hJ π hπ (t • d) =
      gaAffineGroupPoints (borelRootUnipotentGa J hJ π hπ d.val d.property)
        (Multiplicative.ofAdd t) := by
  obtain ⟨n, ρ, hρ, _⟩ :=
    FiniteTypeAffineGroup.exists_injective_matrixDifferential (K := K) (B := B)
  apply faithful_point_matrixMap_injective n ρ hρ
  apply Units.ext
  rw [borelRootUnipotentExponential_matrix]
  rw [GaAffineGroupPoints.matrix_eq_exponential]
  simp only [borelRootUnipotentGa_tangent]
  rfl

end ReductiveGroups
