import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootClosedSubset
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupConjugation

/-!
# Borel Root Subset Torus

Torus covariance of ordered root products: conjugation by a point of the
original split torus multiplies each root parameter by the value of its
character. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "M" => Multiplicative (ι →₀ ℤ)

private abbrev rootTangentSpace (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) := (derivationCompLieHom (B := K)
  (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ)).hom).range

omit [Finite ι] in
/-- Conjugating an ordered root product by a torus point `t` rescales each
parameter by `t` evaluated at the corresponding root character. -/
theorem borelRootSubsetProduct_torus_conj (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
    (hxU : ∀ i, gaAffineGroupTangent (x i) ∈ rootTangentSpace J π hπ)
    (hx : ∀ i, gaAffineGroupTangent (x i) ∈ affineGroupCharacterWeightSpace π i.val)
    (S : Set (borelRootCharacterIndex J π)) (l : List S) (a : S → K)
    (t : WithConv (MonoidAlgebra K M →ₐ[K] K)) :
    AlgHom.mapDomain π t * (borelRootSubsetProduct J π hπ x hxU S l a).val *
        (AlgHom.mapDomain π t)⁻¹ =
      (borelRootSubsetProduct J π hπ x hxU S l
        (fun j => t.ofConv (MonoidAlgebra.single j.val.val 1) * a j)).val := by
  have heach (j : S) : AlgHom.mapDomain π t * gaParameterPoint (x j.val) (a j) *
      (AlgHom.mapDomain π t)⁻¹ =
      gaParameterPoint (x j.val) (t.ofConv (MonoidAlgebra.single j.val.val 1) * a j) :=
    GaAffineGroupPoints.conjugate_of_tangent_eq (x j.val) (x j.val) (AlgHom.mapDomain π t) _
      (AffineGroupAdjoint.eq_character_of_mem_weight π j.val.val t _ (hx j.val)) (a j)
  have h := map_list_prod (MulAut.conj (AlgHom.mapDomain π t)).toMonoidHom
    (l.map fun j => gaParameterPoint (x j.val) (a j))
  simp only [List.map_map, Function.comp_def, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, heach] at h
  exact h

end ReductiveGroups
