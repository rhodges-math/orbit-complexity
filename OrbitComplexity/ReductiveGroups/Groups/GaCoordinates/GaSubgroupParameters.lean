import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductCoordinates
import OrbitComplexity.ReductiveGroups.Groups.Generated.GaGeneratedTangentCriterion
import OrbitComplexity.ReductiveGroups.Groups.Tangents.ClosedSubgroupIntersectionTangent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# Ga Subgroup Parameters

Tangent membership puts all parameters of a Ga morphism
in the same original closed subgroup, over every coefficient algebra. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K B : Type u} [Field K] [CharZero K] [CommRing B] [HopfAlgebra K B]

/-- Tangent containment implies subgroup membership of
every algebra-valued parameter, including nonreduced value algebras. -/
theorem GaParameterPoint.mem_of_tangent_mem_quotient
    (x : B →ₐc[K] SymmetricAlgebra K K) (I : HopfIdeal K B)
    (hx : gaAffineGroupTangent x ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom).range)
    {A : Type*} [CommRing A] [Algebra K A] (a : A) :
    gaParameterPoint x a ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K B) I (CommAlgCat.of K A) := by
  have hkill : ∀ b ∈ I, x b = 0 := by
    apply (gaMorphism_kills_hopfIdeal_iff x I).mpr
    exact (tangent_mem_hopfQuotient_iff I (gaAffineGroupTangent x)).mp hx
  apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr
  intro b hb
  change ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := A)).symm
    (Multiplicative.ofAdd a)).ofConv (x b) = 0
  rw [hkill b hb, map_zero]

/-- A finite ordered product retains membership in the original closed
subgroup when all its Ga tangents belong to that subgroup. -/
theorem GaParameterPoint.prod_mem_of_tangent_mem_quotient
    {κ : Type*} (x : κ → B →ₐc[K] SymmetricAlgebra K K) (I : HopfIdeal K B)
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom).range)
    (l : List κ) {A : Type*} [CommRing A] [Algebra K A] (a : κ → A) :
    (l.map (fun i => gaParameterPoint (x i) (a i))).prod ∈
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
        (CommAlgCat.of K A) := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
  exact GaParameterPoint.mem_of_tangent_mem_quotient (x i) I (hx i) (a i)

end ReductiveGroups
