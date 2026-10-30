import OrbitComplexity.ReductiveGroups.Groups.Characters.CharacterRootIntegration
import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterDifferentialInjective
import OrbitComplexity.ReductiveGroups.Groups.Characters.CharacterWeightDecomposition

/-!
# Character Lie Weight Comparison

Torus-character weight spaces equal the corresponding generalized
Lie root spaces. The comparison includes the identity character. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B ι : Type u} [Field K] [CharZero K] [CommRing B]
  [HopfAlgebra K B] [Algebra.FiniteType K B]

/-- For a closed diagonalizable subgroup with free character lattice, the
character weight submodule is exactly the Lie root submodule for
the derivative of the same character on the tangent image. -/
theorem AffineGroupCharacterWeightSpace.eq_rootSpace
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) (α : Multiplicative (ι →₀ ℤ)) :
    affineGroupCharacterWeightSpace π α =
      (LieAlgebra.rootSpace (diagonalizableTangentImage π)
        (characterDifferentialOnImage π hπ α)).toSubmodule := by
  let χ : Multiplicative (ι →₀ ℤ) → diagonalizableTangentImage π → K :=
    fun β => characterDifferentialOnImage π hπ β
  have hχ : Function.Injective χ :=
    DFunLike.coe_injective.comp (characterDifferentialOnImage_injective π hπ)
  have hi : iSupIndep (fun β : Multiplicative (ι →₀ ℤ) =>
      (LieAlgebra.rootSpace (diagonalizableTangentImage π) (χ β)).toSubmodule) := by
    rw [LieSubmodule.iSupIndep_toSubmodule]
    exact (LieModule.iSupIndep_genWeightSpace K (diagonalizableTangentImage π)
      (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))).comp hχ
  have heq := (hi.le_iff_eq_of_iSup_eq_top
    (ISup.affineGroupCharacterWeightSpace_eq_top π)).mp
      (show (fun β => affineGroupCharacterWeightSpace π β) ≤
        (fun β => (LieAlgebra.rootSpace (diagonalizableTangentImage π)
          (χ β)).toSubmodule) from fun β d hd => characterWeight_mem_rootSpace π hπ β d hd)
  exact congrFun heq α

end ReductiveGroups
