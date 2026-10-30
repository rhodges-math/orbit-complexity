import OrbitComplexity.ReductiveGroups.Groups.Characters.CharacterWeightDecomposition

/-!
# Independence of torus-character tangent subspaces

The character-weight decomposition of the cotangent dual transports to the
tangent derivations by the canonical cotangent linear equivalence. Distinct
character subspaces therefore form an independent family.

## Main results

* `ReductiveGroups.AffineGroupCharacterWeights.iSupIndep`: independence of all character spaces.
-/

noncomputable section

namespace ReductiveGroups

universe u

variable {K B M : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B] [CommGroup M]

/-- The tangent character-weight subspaces of a finite type affine group are independent. -/
theorem AffineGroupCharacterWeights.iSupIndep (π : B →ₐc[K] MonoidAlgebra K M) :
    iSupIndep (fun α => affineGroupCharacterWeightSpace π α) := by
  classical
  let e := Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)
  have hweight (α : M) : affineGroupCharacterWeightSpace π α =
      (Derivation.adjointWeightSpace π α).map e.toLinearMap :=
    (Submodule.map_equiv_eq_comap_symm e _).symm
  simp_rw [hweight]
  exact (Derivation.isInternal_adjointWeightSpace π).submodule_iSupIndep.map_orderIso
    (Submodule.orderIsoMapComap e)

end ReductiveGroups
