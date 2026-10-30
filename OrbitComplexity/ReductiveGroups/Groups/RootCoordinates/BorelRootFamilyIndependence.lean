import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootPairIndependence

/-!
# Borel Root Family Independence

Occurring characters of the maximal torus whose roots are
linearly independent over `K` are linearly independent over `ℤ` in the
character lattice. -/

noncomputable section
namespace ReductiveGroups

open TauCeti LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Characters with `K`-independent roots are `ℤ`-independent. -/
theorem OccurringCharacter.family_linearIndependent
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    letI := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    letI := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    letI := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    ∀ {S : Type*} (α : S → {α : M // affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1}),
      LinearIndependent K (fun s => (rootSystem (centerQuotientCartan
        (diagonalizableTangentImage π))).root
          (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB (α s))) →
      LinearIndependent ℤ (fun s => Multiplicative.toAdd (α s).val) := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  intro S α hind
  let H := diagonalizableTangentImage π
  let P := rootSystem (centerQuotientCartan H)
  let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
  have hr (s : S) (t : H) :
      P.root (E (α s)) (centerQuotientCartanMap H t) =
        characterDifferentialOnImage π hπ (α s).val t :=
    ReductiveCharacterCenterQuotientRootEquiv.apply_map I hI π hπ hker hB (α s) t
  rw [linearIndependent_iff']
  intro s g hg i hi
  have happ : ∑ k ∈ s, g k • characterDifferentialOnImageHom π hπ
      (Multiplicative.toAdd (α k).val) = 0 := by
    rw [← map_zero (characterDifferentialOnImageHom π hπ), ← hg, map_sum]
    simp only [map_zsmul]
  have hK : ∑ k ∈ s, (g k : K) • P.root (E (α k)) = 0 := by
    ext h
    obtain ⟨u, rfl⟩ := centerQuotientCartanMap_surjective H h
    have hu := LinearMap.congr_fun happ u
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] at hu ⊢
    simp only [hr]
    change ∑ k ∈ s, g k • characterDifferentialOnImage π hπ (α k).val u = 0 at hu
    simpa only [zsmul_eq_mul, smul_eq_mul] using hu
  have := linearIndependent_iff'.mp hind s (fun k => (g k : K)) hK i hi
  exact_mod_cast this

end ReductiveGroups
