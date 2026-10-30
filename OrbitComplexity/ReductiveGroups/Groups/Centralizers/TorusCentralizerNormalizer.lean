import OrbitComplexity.ReductiveGroups.Groups.Centralizers.TorusCentralizerTangent

/-!
# Torus Centralizer Normalizer

The torus centralizer tangent is the zero root subalgebra, hence
self-normalizing, with an arbitrary choice of that it equals the torus tangent. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

/-- The exact centralizer tangent image is the zero root subalgebra
of the original torus tangent inside the original ambient Lie algebra. -/
theorem TorusConjugationFixed.tangentImage_eq_zeroRootSubalgebra
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) :
    (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (torusConjugationFixedHopfIdeal π)).hom).range =
      LieAlgebra.zeroRootSubalgebra K
        (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
        (diagonalizableTangentImage π) := by
  rw [← LieSubalgebra.toSubmodule_inj]
  rw [TorusConjugationFixed.tangentImage_eq_identityWeight,
    AffineGroupIdentityWeight.eq_rootSpace_zero π hπ]
  rfl

/-- The torus centralizer is self-normalizing at the Lie-algebra level. With nilpotence it
gives the Cartan property; see `Groups/TorusCentralizerJordan.lean` and
`Groups/MaximalTorusLieCartan.lean`. -/
theorem TorusConjugationFixed.tangentImage_normalizer
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) :
    (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (torusConjugationFixedHopfIdeal π)).hom).range.normalizer =
    (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (torusConjugationFixedHopfIdeal π)).hom).range := by
  rw [TorusConjugationFixed.tangentImage_eq_zeroRootSubalgebra π hπ]
  exact LieAlgebra.zeroRootSubalgebra_normalizer_eq_self K _ _

end ReductiveGroups
