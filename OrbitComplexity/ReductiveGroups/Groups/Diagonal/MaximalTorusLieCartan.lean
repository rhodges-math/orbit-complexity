import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusSemisimpleCommonBasis
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.MaximalTorusCommonEigenbasis
import OrbitComplexity.ReductiveGroups.Groups.Centralizers.TorusCentralizerMatrix
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusQuotientTangent

/-!
# Maximal Torus Lie Cartan

The tangent image of the original maximal torus in a reductive
affine group is Cartan.  -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- A semisimple original tangent centralizing the fixed maximal torus
belongs to its tangent image. The common basis is constructed from the
represented torus action. -/
theorem MaximalTorus.semisimpleCentralizer_mem_tangent
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (d : 𝔤) (hd : d ∈ torusCentralizerTangent π)
    (hs : Module.End.IsSemisimple (Matrix.toLin' (affineGroupMatrixDifferential n ρ d))) :
    d ∈ diagonalizableTangentImage π := by
  have hc : ∀ g : WithConv (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K),
      Commute (TauCeti.GeneralLinear.pointsMulEquiv n
        (TauCeti.AlgHom.mapDomain (π.comp ρ) g) : Matrix (Fin n) (Fin n) K)
        (affineGroupMatrixDifferential n ρ d) := by
    intro g
    simpa only [TauCeti.AlgHom.mapDomain_comp, MonoidHom.comp_apply] using
      (torusCentralizer_mem_iff_matrix_commute π n ρ hρ d).mp hd g
  obtain ⟨b, hb, hbd⟩ := exists_torusSemisimple_commonBasis n (π.comp ρ)
    (affineGroupMatrixDifferential n ρ d) hs hc
  apply MaximalTorus.tangent_mem_image_of_common_eigenbasis I hI π hπ hker
    n ρ hρ b ?_ d hbd
  intro p
  exact hb (WithConv.toConv p)

/-- The torus-centralizer tangent equals the maximal torus
tangent, under geometric reductivity of the original group. -/
theorem MaximalTorusLieCartan.maximalTorusCentralizer_eq_torus
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B)) :
    torusCentralizerTangent π = diagonalizableTangentImage π := by
  obtain ⟨V, n, b, hρ⟩ :=
    TauCeti.Comodule.exists_coordinateBialgHom_surjective (k := K) (H := B)
  apply TorusCentralizerJordan.eq_torus_of_semisimple_mem π hπ n
    (TauCeti.Comodule.coordinateBialgHom (H := B) b) hρ hB
  intro d hd hs
  exact MaximalTorus.semisimpleCentralizer_mem_tangent I hI π hπ hker n
    (TauCeti.Comodule.coordinateBialgHom (H := B) b) hρ d hd hs

/-- For these parameters,

```lean
(diagonalizableTangentImage π).IsCartanSubalgebra
```
-/
theorem MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B)) :
    (diagonalizableTangentImage π).IsCartanSubalgebra := by
  apply (torusTangent_isCartan_iff_identityWeight π hπ).mpr
  rw [← TorusConjugationFixed.tangentImage_eq_identityWeight]
  exact congrArg LieSubalgebra.toSubmodule
    (MaximalTorusLieCartan.maximalTorusCentralizer_eq_torus I hI π hπ hker hB)

/-- The coordinate-free endpoint retains the original maximal torus Hopf
ideal and its original quotient differential. Split coordinates and a
faithful representation are chosen and proved only inside the proof. -/
theorem reductive_maximalTorus_tangent_isCartan
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B)) :
    (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient
        (CommHopfAlgCat.of K B) I).hom).range.IsCartanSubalgebra := by
  obtain ⟨r, π, hπ, hker, heq⟩ := TorusQuotientTangent.exists_tangentImage
    (TauCeti.FiniteTypeCommHopfAlgCat.of K B) I hI
  rw [← heq]
  exact MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB

end ReductiveGroups
