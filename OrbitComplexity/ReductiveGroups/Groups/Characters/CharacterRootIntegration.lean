import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterWeightDifferential
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTangentImage
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTangentCharacters
import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupRootIntegration

/-!
# Character Root Integration

Integrating nontrivial torus-character weight vectors in the
original group. Character weights are compared to Lie root spaces by
differentiating the adjoint action. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B M : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B] [CommGroup M]

/-- A character weight vector is a Lie root vector for the
tangent image and the differential of that same character. -/
theorem characterWeight_mem_rootSpace
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π) (α : M)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (hd : d ∈ affineGroupCharacterWeightSpace π α) :
    d ∈ LieAlgebra.rootSpace (diagonalizableTangentImage π)
      (characterDifferentialOnImage π hπ α) := by
  apply (LieModule.mem_genWeightSpace _ _ _).mpr
  intro x
  obtain ⟨h, rfl⟩ := (diagonalizableTangentEquivImage π hπ).surjective x
  refine ⟨1, ?_⟩
  change ⁅(diagonalizableTangentEquivImage π hπ h :
      Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)), d⁆ -
    characterDifferentialOnImage π hπ α (diagonalizableTangentEquivImage π hπ h) • d = 0
  rw [diagonalizableTangentEquivImage_coe,
    characterDifferentialOnImage_apply_equiv, bracket_eq_character_derivative π α h d hd,
    characterDifferential_apply, sub_self]

/-- A character with nonzero differential gives unique additive-group
integration of each weight vector, inside the original group. -/
theorem CharacterRootIntegration.existsUnique_of_characterWeight
    [CharZero K] [IsAlgClosed K]
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π) (α : M)
    (hα : characterDifferential (K := K) α ≠ 0)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (hd : d ∈ affineGroupCharacterWeightSpace π α) :
    ∃! x : B →ₐc[K] SymmetricAlgebra K K, gaAffineGroupTangent x = d := by
  apply existsUnique_gaMorphism_of_mem_rootSpace (diagonalizableTangentImage π)
    (characterDifferentialOnImage π hπ α)
  · intro hz
    apply characterDifferentialOnImage_ne_zero π hπ α hα
    ext y
    exact congrFun hz y
  · exact characterWeight_mem_rootSpace π hπ α d hd

/-- For a free character lattice in characteristic zero, nonidentity of the
character alone supplies the required nonzero differential. -/
theorem CharacterRootIntegration.existsUnique_of_latticeCharacterWeight
    [CharZero K] [IsAlgClosed K] {ι : Type u}
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) (α : Multiplicative (ι →₀ ℤ)) (hα : α ≠ 1)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (hd : d ∈ affineGroupCharacterWeightSpace π α) :
    ∃! x : B →ₐc[K] SymmetricAlgebra K K, gaAffineGroupTangent x = d := by
  exact CharacterRootIntegration.existsUnique_of_characterWeight π hπ α
    (characterDifferential_ne_zero_of_ne_one α hα) d hd

end ReductiveGroups
