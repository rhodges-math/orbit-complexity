import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalTorusPointsCriterion
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalTorusSubgroup
import OrbitComplexity.ReductiveGroups.Groups.Representations.FaithfulDiagonalIntersection
import OrbitComplexity.ReductiveGroups.Groups.Tangents.AffineGroupMatrixDifferential

/-!
# Maximal Torus Diagonal Embedding

A maximal torus inside the original affine group absorbs a
faithful diagonalizable intersection. Pointwise diagonality is upgraded to
a coordinate-ideal inclusion before maximality is applied. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- If the original torus points have diagonal image under a faithful GL
coordinate representation, then every original tangent with diagonal matrix
belongs to the original maximal torus quotient tangent image. -/
theorem MaximalTorus.tangent_of_diagonal_embedding
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (_hπ : Function.Surjective π)
    (hker : ∀ b : B, π b = 0 ↔ b ∈ I.toIdeal)
    (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (hdiag : ∀ p : MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K,
      ∃ v : Fin n → K,
        ((TauCeti.GeneralLinear.pointsMulEquiv n
          (WithConv.toConv (p.comp (π.comp ρ).toAlgHom)) :
          Matrix.GeneralLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) = Matrix.diagonal v)
    (d : 𝔤)
    (hd : ∃ v : Fin n → K,
      affineGroupMatrixDifferential n ρ d = Matrix.diagonal v) :
    d ∈ (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom).range := by
  let A := TauCeti.FiniteTypeCommHopfAlgCat.of K
    (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
  let C := TauCeti.FiniteTypeCommHopfAlgCat.of K B
  let J := diagonalMatrixHopfIdeal (K := K) n
  have hJI : J.map ρ ≤ I := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := (TauCeti.HopfIdeal.mem_map_iff_of_surjective hρ).mp hb
    have hδ : (diagonalTorusCoordinateMap (R := K) (N := n)).hom a = 0 :=
      (TauCeti.HopfIdeal.mem_kerOfSurjective
        (diagonalTorusCoordinateMap (R := K) (N := n)).hom
        diagonalTorusCoordinateMap_surjective).mp ha
    have hφ : (π.comp ρ) a = 0 :=
      DiagonalTorusCoordinateMap.ker_le_of_diagonal_points n (π.comp ρ) hdiag a hδ
    exact (hker (ρ a)).mp hφ
  have hmatrix : ∀ i j : Fin n, i ≠ j →
      TauCeti.GeneralLinear.tangentMatrix n
        (TauCeti.derivationComp (B := K) ρ d) i j = 0 := by
    obtain ⟨v, hv⟩ := hd
    intro i j hij
    rw [affineGroupMatrixDifferential_apply] at hv
    rw [hv, Matrix.diagonal_apply_ne _ hij]
  have hJt : TauCeti.derivationComp (B := K) ρ d ∈
      (TauCeti.derivationCompLieHom (B := K)
        (TauCeti.CommHopfAlgCat.mkQuotient A.obj J).hom).range :=
    (DiagonalTorusSubgroup.diagonalMatrixHopfQuotient_iff_matrix n _).mpr hmatrix
  exact MaximalTorus.of_faithful_diagonalizableIntersection
    A C ρ hρ I J hI hJI
    (DiagonalMatrixHopfIdeal.quotient_groupLikeSpanned n) d hJt

/-- The same conclusion in the fixed split-coordinate tangent image.
The original maximal torus ideal and original ambient group remain fixed. -/
theorem MaximalTorus.diagonal_embedding_tangent_mem_image
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ b : B, π b = 0 ↔ b ∈ I.toIdeal)
    (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (hdiag : ∀ p : MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K,
      ∃ v : Fin n → K,
        ((TauCeti.GeneralLinear.pointsMulEquiv n
          (WithConv.toConv (p.comp (π.comp ρ).toAlgHom)) :
          Matrix.GeneralLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) = Matrix.diagonal v)
    (d : 𝔤)
    (hd : ∃ v : Fin n → K,
      affineGroupMatrixDifferential n ρ d = Matrix.diagonal v) :
    d ∈ diagonalizableTangentImage π := by
  have hInear := MaximalTorus.tangent_of_diagonal_embedding I hI π hπ hker
    n ρ hρ hdiag d hd
  apply (tangent_mem_range_iff_kills_kernel π hπ d).mpr
  intro b hb
  have hbi : b ∈ I.toIdeal := (hker b).mp hb
  exact (tangent_mem_hopfQuotient_iff I d).mp hInear b hbi

end ReductiveGroups
