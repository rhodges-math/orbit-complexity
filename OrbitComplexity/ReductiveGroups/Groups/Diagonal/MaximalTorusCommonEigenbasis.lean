import OrbitComplexity.ReductiveGroups.Groups.Representations.ConjugatedMatrixRepresentation
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.MaximalTorusDiagonalEmbedding
import OrbitComplexity.ReductiveGroups.Lie.Roots.MatrixBasisConjugation

/-!
# Maximal Torus Common Eigenbasis

A common eigenbasis for the torus and a tangent vector gives
membership in that same maximal torus's tangent space. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- A common matrix basis for all torus points and one original tangent
forces that tangent into the maximal torus. -/
theorem MaximalTorus.tangent_mem_image_of_common_eigenbasis
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (b : Module.Basis (Fin n) K (Fin n → K))
    (hdiag : ∀ p : MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K,
      ∃ v : Fin n → K,
        LinearMap.toMatrix b b (Matrix.toLin'
          (((TauCeti.GeneralLinear.pointsMulEquiv n
            (WithConv.toConv (p.comp (π.comp ρ).toAlgHom)) :
            Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K))) =
          Matrix.diagonal v)
    (d : 𝔤)
    (hd : ∃ v : Fin n → K,
      LinearMap.toMatrix b b (Matrix.toLin' (affineGroupMatrixDifferential n ρ d)) =
        Matrix.diagonal v) :
    d ∈ diagonalizableTangentImage π := by
  obtain ⟨P, hP⟩ := exists_matrixBasisConjugation n b
  let g : WithConv (TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] K) :=
    (TauCeti.GeneralLinear.pointsMulEquiv n).symm P
  let ρ' := ρ.comp (affineGroupConjugationBialgHom g)
  have hg : TauCeti.GeneralLinear.pointsMulEquiv n g = P := by
    exact MulEquiv.apply_symm_apply _ P
  have hρ' : Function.Surjective ρ' :=
    conjugatedMatrixCoordinateMap_surjective n ρ g hρ
  have hdiag' : ∀ p : MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K,
      ∃ v : Fin n → K,
        ((TauCeti.GeneralLinear.pointsMulEquiv n
          (WithConv.toConv (p.comp (π.comp ρ').toAlgHom)) :
          Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          Matrix.diagonal v := by
    intro p
    obtain ⟨v, hv⟩ := hdiag p
    refine ⟨v, ?_⟩
    let q : WithConv (B →ₐ[K] K) := WithConv.toConv (p.comp π.toAlgHom)
    have hq : TauCeti.AlgHom.mapDomain ρ q =
        WithConv.toConv (p.comp (π.comp ρ).toAlgHom) := by
      apply WithConv.ofConv_injective
      ext a
      rfl
    have hq' : TauCeti.AlgHom.mapDomain ρ' q =
        WithConv.toConv (p.comp (π.comp ρ').toAlgHom) := by
      apply WithConv.ofConv_injective
      ext a
      rfl
    have hc := conjugatedMatrixCoordinateMap_point n ρ g q
    rw [hq, hq', hg] at hc
    have hcm := congrArg (fun A : Matrix.GeneralLinearGroup (Fin n) K =>
      (A : Matrix (Fin n) (Fin n) K)) hc
    calc
      _ = (P : Matrix (Fin n) (Fin n) K) *
          ((TauCeti.GeneralLinear.pointsMulEquiv n
            (WithConv.toConv (p.comp (π.comp ρ).toAlgHom)) :
            Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (↑P⁻¹ : Matrix (Fin n) (Fin n) K) := by
            simpa only [Matrix.GeneralLinearGroup.coe_mul] using hcm
      _ = Matrix.diagonal v := by rw [hP, hv]
  have hd' : ∃ v : Fin n → K,
      affineGroupMatrixDifferential n ρ' d = Matrix.diagonal v := by
    obtain ⟨v, hv⟩ := hd
    refine ⟨v, ?_⟩
    rw [conjugatedMatrixCoordinateMap_tangent n ρ g d, hg, hP, hv]
  exact MaximalTorus.diagonal_embedding_tangent_mem_image I hI π hπ hker
    n ρ' hρ' hdiag' d hd'

end ReductiveGroups
