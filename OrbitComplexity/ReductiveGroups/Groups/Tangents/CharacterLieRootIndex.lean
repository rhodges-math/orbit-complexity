import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterLieWeightComparison
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusZeroWeight

/-!
# Character Lie Root Index

Occurring Lie weights for the split torus are exactly the
differentials of occurring algebraic characters. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B ι : Type u} [Field K] [CommRing B]
  [HopfAlgebra K B] [Algebra.FiniteType K B]

private abbrev GroupTangent (K B : Type u) [Field K] [CommRing B]
    [HopfAlgebra K B] :=
  Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- Every occurring Lie weight is the differential of a unique character
whose character space is nonzero. -/
theorem existsUnique_character_of_lieWeight
    [CharZero K]
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (χ : LieModule.Weight K (diagonalizableTangentImage π) (GroupTangent K B)) :
    ∃! α : Multiplicative (ι →₀ ℤ),
      affineGroupCharacterWeightSpace π α ≠ ⊥ ∧
      (χ : diagonalizableTangentImage π → K) =
        (characterDifferentialOnImage π hπ α : diagonalizableTangentImage π → K) := by
  let H := diagonalizableTangentImage π
  let M := GroupTangent K B
  let f : Multiplicative (ι →₀ ℤ) → H → K :=
    fun α => characterDifferentialOnImage π hπ α
  have hspan : ⨆ α, LieModule.genWeightSpace M (f α) = ⊤ := by
    apply LieSubmodule.iSup_toSubmodule_eq_top.mp
    calc
      (⨆ α, (LieModule.genWeightSpace M (f α) : Submodule K M)) =
          ⨆ α, affineGroupCharacterWeightSpace π α := by
            apply iSup_congr
            intro α
            exact (AffineGroupCharacterWeightSpace.eq_rootSpace π hπ α).symm
      _ = ⊤ := ISup.affineGroupCharacterWeightSpace_eq_top π
  have hind : iSupIndep (fun ψ : H → K => LieModule.genWeightSpace M ψ) :=
    LieModule.iSupIndep_genWeightSpace K H M
  have hmem : (χ : H → K) ∈ Set.range f := by
    apply hind.mem_of_biSup_eq_top
    · simpa only [iSup_range] using hspan
    · exact χ.genWeightSpace_ne_bot
  obtain ⟨α, hα⟩ := hmem
  refine ⟨α, ?_, ?_⟩
  · constructor
    · rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ]
      intro hh
      have hh' := (LieSubmodule.toSubmodule_eq_bot
        (LieModule.genWeightSpace M (f α))).mp hh
      apply χ.genWeightSpace_ne_bot
      simpa only [hα] using hh'
    · exact hα.symm
  · intro β hβ
    exact characterDifferentialOnImage_injective π hπ
      (DFunLike.coe_injective (hβ.2.symm.trans hα.symm))

/-- Occurring algebraic characters index precisely all occurring Lie weights
of the original tangent algebra under the closed split torus. -/
def occurringCharacterLieWeightEquiv
    [CharZero K]
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) :
    {α : Multiplicative (ι →₀ ℤ) // affineGroupCharacterWeightSpace π α ≠ ⊥} ≃
      LieModule.Weight K (diagonalizableTangentImage π) (GroupTangent K B) := by
  let F : {α : Multiplicative (ι →₀ ℤ) //
      affineGroupCharacterWeightSpace π α ≠ ⊥} →
      LieModule.Weight K (diagonalizableTangentImage π) (GroupTangent K B) :=
    fun α => ⟨characterDifferentialOnImage π hπ α, by
      intro hz
      apply α.property
      rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ]
      exact (LieSubmodule.toSubmodule_eq_bot _).mpr hz⟩
  apply Equiv.ofBijective F
  constructor
  · intro α β hab
    apply Subtype.ext
    apply characterDifferentialOnImage_injective π hπ
    exact DFunLike.coe_injective (congrArg
      (fun χ : LieModule.Weight K (diagonalizableTangentImage π)
        (GroupTangent K B) => (χ : diagonalizableTangentImage π → K)) hab)
  · intro χ
    obtain ⟨α, ⟨hα, hχ⟩, _⟩ := existsUnique_character_of_lieWeight π hπ χ
    refine ⟨⟨α, hα⟩, ?_⟩
    apply LieModule.Weight.ext
    intro x
    exact (congrFun hχ x).symm

omit [Algebra.FiniteType K B] in
/-- Under the index equivalence, the zero Lie weight is exactly the identity
character. This also covers a possibly non-occurring identity character. -/
theorem characterDifferentialOnImage_eq_zero_iff
    [CharZero K]
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) (α : Multiplicative (ι →₀ ℤ)) :
    characterDifferentialOnImage π hπ α = 0 ↔ α = 1 := by
  constructor
  · intro h
    apply characterDifferentialOnImage_injective π hπ
    simpa only [characterDifferentialOnImage_one] using h
  · rintro rfl
    exact characterDifferentialOnImage_one π hπ

end ReductiveGroups
