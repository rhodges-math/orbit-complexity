import OrbitComplexity.ReductiveGroups.Groups.Unipotent.BorelRootUnipotentSubgroup

/-!
# Borel Root Point Unipotence

The Borel's Ga-only subgroup satisfies the uniform matrix
unipotence equation in every representation and every value algebra. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u w
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Membership in the subgroup, rather than in a word
description, implies matrix unipotence with exponent equal to matrix size. -/
theorem BorelRootUnipotentPoint.matrix_pow_sub_one_eq_zero
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    {A : Type w} [CommRing A] [Algebra K A]
    (g : WithConv (B →ₐ[K] A))
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K A)) :
    ((GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g) :
      Matrix (Fin n) (Fin n) A) - 1) ^ n = 0 := by
  let S := (derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
  let : LieAlgebra.IsSolvable S := borel_tangentImage_isSolvable J hJ
  let q := (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ)).hom
  obtain ⟨v, hv⟩ := hg
  have hgv : AlgHom.mapDomain q v = g := hv
  have h := SolvableGaGeneratedQuotient.matrix_uniform_unipotent
    (borelRootVectorGa J π hπ) S
    (fun r => by rw [borelRootVectorGa_tangent]; exact r.2.property.2.2) n ρ v
  have hcomp : AlgHom.mapDomain (q.comp ρ) v = AlgHom.mapDomain ρ g := by
    rw [← hgv, AlgHom.mapDomain_comp]
    rfl
  change ((GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain (q.comp ρ) v) :
    Matrix (Fin n) (Fin n) A) - 1) ^ n = 0 at h
  rw [hcomp] at h
  exact h

end ReductiveGroups
