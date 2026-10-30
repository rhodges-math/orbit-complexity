import OrbitComplexity.ReductiveGroups.Groups.Exponential.BorelRootExponentialLaws
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootPointUnipotence
import OrbitComplexity.ReductiveGroups.Groups.Additive.UnipotentPointGaIntegration
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaUnitPointSubgroupCriterion

/-!
# Borel Root Exponential Bijection

The Borel Ga-only subgroup has bijective exponential coordinates
on K-points. All group points and tangents are those of the original group;
regular coordinates and ordered root-product coordinates are in
`Groups/BorelRootLogarithmCoordinateMap.lean` and
`Groups/BorelRootOrderedChart.lean`. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Every original point of the Borel's Ga-only subgroup lies at
parameter one on exactly one Ga morphism of the original group. -/
theorem BorelRootExponentialBijection.existsUnique_of_borelRootUnipotentPoint
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (g : WithConv (B →ₐ[K] K))
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K)) :
    ∃! x : B →ₐc[K] SymmetricAlgebra K K,
      gaAffineGroupPoints x (Multiplicative.ofAdd 1) = g := by
  obtain ⟨V, n, b, hρ⟩ := Comodule.exists_coordinateBialgHom_surjective (k := K) (H := B)
  apply UnipotentPointGaIntegration.existsUnique_of_matrix_point_unipotent n
    (Comodule.coordinateBialgHom b) hρ g
  exact ⟨n, BorelRootUnipotentPoint.matrix_pow_sub_one_eq_zero J hJ π hπ n
    (Comodule.coordinateBialgHom b) g hg⟩

/-- Every point of the subgroup is the exponential of a
subgroup tangent. This is a global statement on K-points. -/
theorem BorelRootUnipotentExponential.surjective_to_subgroup
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (g : WithConv (B →ₐ[K] K))
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K)) :
    ∃ d, borelRootUnipotentExponential J hJ π hπ d = g := by
  obtain ⟨x, hx, _⟩ := BorelRootExponentialBijection.existsUnique_of_borelRootUnipotentPoint
    J hJ π hπ g hg
  have hkill : ∀ b ∈ borelRootUnipotentHopfIdeal J π hπ, x b = 0 := by
    apply (GaMorphism.kills_hopfIdeal_iff_unitPoint_mem x _).mpr
    rw [hx]
    exact hg
  have hd : gaAffineGroupTangent x ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range := by
    apply (tangent_mem_hopfQuotient_iff _ _).mpr
    exact (gaMorphism_kills_hopfIdeal_iff x _).mp hkill
  refine ⟨⟨gaAffineGroupTangent x, hd⟩, ?_⟩
  have hchosen : borelRootUnipotentGa J hJ π hπ (gaAffineGroupTangent x) hd = x := by
    apply gaMorphism_ext_of_tangent_eq
    exact borelRootUnipotentGa_tangent J hJ π hπ (gaAffineGroupTangent x) hd
  simpa only [borelRootUnipotentExponential, hchosen] using hx

/-- Exponential identifies the tangent space with the
Ga-only subgroup's K-points as sets. This is a bijection of sets, not a
group isomorphism or an isomorphism of coordinate rings. -/
def borelRootUnipotentExponentialEquiv
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π) :
    (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range ≃
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K) :=
  Equiv.ofBijective
    (fun d => ⟨borelRootUnipotentExponential J hJ π hπ d,
      borelRootUnipotentExponential_mem J hJ π hπ d⟩)
    ⟨by
      intro d e h
      exact borelRootUnipotentExponential_injective J hJ π hπ (congrArg Subtype.val h),
    by
      intro g
      obtain ⟨d, hd⟩ := BorelRootUnipotentExponential.surjective_to_subgroup
        J hJ π hπ g.val g.property
      exact ⟨d, Subtype.ext hd⟩⟩

end ReductiveGroups
