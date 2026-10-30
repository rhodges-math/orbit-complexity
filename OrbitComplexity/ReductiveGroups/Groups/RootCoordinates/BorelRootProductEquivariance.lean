import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootProductLogarithm
import OrbitComplexity.ReductiveGroups.Groups.Exponential.BorelRootExponentialConjugation

/-!
# Borel Root Product Equivariance

Adjoint eigenvector equations imply diagonal equivariance of the
polynomial obtained from the ordered Ga product and logarithm. -/

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

/-- This is equivariance of the coordinate polynomial. Its
hypotheses are adjoint equations on the original group and tangent,
not an assumed equivariance or homogeneity property of that polynomial. -/
theorem BorelRootProductLogarithm.diagonal_equivariant
    (x : κ → B →ₐc[K] SymmetricAlgebra K K)
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    (l : List κ) (f : rootTangentSpace J π hπ →ₗ[K] K)
    (g : WithConv (B →ₐ[K] K))
    (hAd : ∀ d : rootTangentSpace J π hπ,
      affineGroupAdjointRepresentation g d.val ∈ rootTangentSpace J π hπ)
    (c : κ → K) (β : K)
    (hxeigen : ∀ i, affineGroupAdjointRepresentation g (gaAffineGroupTangent (x i)) =
      c i • gaAffineGroupTangent (x i))
    (hfeigen : ∀ d : rootTangentSpace J π hπ,
      f ⟨affineGroupAdjointRepresentation g d.val, hAd d⟩ = β * f d)
    (a : κ → K) :
    MvPolynomial.aeval (fun i => c i * a i)
        (borelRootProductLogarithm J hJ π hπ x l f) =
      β * MvPolynomial.aeval a (borelRootProductLogarithm J hJ π hπ x l f) := by
  let u : CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K) :=
    ⟨(l.map (fun i => gaParameterPoint (x i) (a i))).prod,
      GaParameterPoint.prod_mem_of_tangent_mem_quotient x
        (borelRootUnipotentHopfIdeal J π hπ) hx l a⟩
  let v : CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K) :=
    ⟨(l.map (fun i => gaParameterPoint (x i) (c i * a i))).prod,
      GaParameterPoint.prod_mem_of_tangent_mem_quotient x
        (borelRootUnipotentHopfIdeal J π hπ) hx l (fun i => c i * a i)⟩
  have heach (i : κ) : g * gaParameterPoint (x i) (a i) * g⁻¹ =
      gaParameterPoint (x i) (c i * a i) :=
    GaAffineGroupPoints.conjugate_of_tangent_eq (x i) (x i) g (c i) (hxeigen i) (a i)
  have hprod : g * u.val * g⁻¹ = v.val := by
    have h := map_list_prod (MulAut.conj g).toMonoidHom
      (l.map (fun i => gaParameterPoint (x i) (a i)))
    simpa only [List.map_map, Function.comp_def, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, heach] using h
  obtain ⟨hu, hlog⟩ := BorelRootUnipotentExponentialEquiv.symm_conjugate
    J hJ π hπ g hAd u
  have hv : v = ⟨g * u.val * g⁻¹, hu⟩ := Subtype.ext hprod.symm
  rw [borelRootProductLogarithm_eval J hJ π hπ x hx,
    borelRootProductLogarithm_eval J hJ π hπ x hx]
  change f ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm v) =
    β * f ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm u)
  rw [hv, hlog]
  exact hfeigen _

end ReductiveGroups
