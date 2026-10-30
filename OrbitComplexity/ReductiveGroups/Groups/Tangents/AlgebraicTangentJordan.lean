import OrbitComplexity.ReductiveGroups.Groups.Representations.GLTruncationStability
import OrbitComplexity.ReductiveGroups.Groups.Representations.GLCoordinateNilpotent
import OrbitComplexity.ReductiveGroups.Groups.Representations.GLCoordinateCommutation
import OrbitComplexity.ReductiveGroups.Groups.Representations.GLCoordinateSemisimple
import OrbitComplexity.ReductiveGroups.Groups.TangentOperators.LeftTangentLinearity
import OrbitComplexity.ReductiveGroups.Groups.Tangents.TangentJordanKernel

/-!
# Algebraic Tangent Jordan

Matrix Jordan parts descend through the original coordinate kernel. -/

noncomputable section
namespace ReductiveGroups

variable {K B : Type*} [Field K] [PerfectField K]
  [CommRing B] [HopfAlgebra K B]

private theorem AlgebraicTangentJordan.of_semisimple_restrictions
    (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (Xn Xs : Matrix (Fin n) (Fin n) K)
    (hadd : Xn + Xs = TauCeti.GeneralLinear.tangentMatrix n
      (TauCeti.derivationComp (B := K) ρ d))
    (hcomm : Commute Xn Xs) (hn : IsNilpotent Xn)
    (hsfinite : ∀ r bound : ℕ,
      let ds := (TauCeti.GeneralLinear.tangentLinearEquivMatrix
        (R := K) (B := K) n).symm Xs
      let W := glCoordinateTruncation (K := K) n r bound
      let hW : W ∈ (leftTangentOperator ds).invtSubmodule := by
        intro b hb
        exact LeftTangentOperator.preserves_glCoordinateTruncation n ds r bound b hb
      Module.End.IsSemisimple ((leftTangentOperator ds).restrict hW)) :
    (TauCeti.GeneralLinear.tangentLinearEquivMatrix
      (R := K) (B := K) n).symm Xn ∈
        (TauCeti.derivationCompLieHom (B := K) ρ).range ∧
    (TauCeti.GeneralLinear.tangentLinearEquivMatrix
      (R := K) (B := K) n).symm Xs ∈
        (TauCeti.derivationCompLieHom (B := K) ρ).range := by
  let da := TauCeti.derivationComp (B := K) ρ d
  let dn := (TauCeti.GeneralLinear.tangentLinearEquivMatrix
    (R := K) (B := K) n).symm Xn
  let ds := (TauCeti.GeneralLinear.tangentLinearEquivMatrix
    (R := K) (B := K) n).symm Xs
  have hdn : TauCeti.GeneralLinear.tangentMatrix n dn = Xn := by
    rw [← TauCeti.GeneralLinear.tangentLinearEquivMatrix_apply]
    exact (TauCeti.GeneralLinear.tangentLinearEquivMatrix
      (R := K) (B := K) n).apply_symm_apply Xn
  have hds : TauCeti.GeneralLinear.tangentMatrix n ds = Xs := by
    rw [← TauCeti.GeneralLinear.tangentLinearEquivMatrix_apply]
    exact (TauCeti.GeneralLinear.tangentLinearEquivMatrix
      (R := K) (B := K) n).apply_symm_apply Xs
  have hsumDer : da = dn + ds := by
    apply (TauCeti.GeneralLinear.tangentLinearEquivMatrix
      (R := K) (B := K) n).injective
    simp only [map_add, TauCeti.GeneralLinear.tangentLinearEquivMatrix_apply]
    rw [hdn, hds]
    exact hadd.symm
  have hcommOp : Commute (leftTangentOperator dn) (leftTangentOperator ds) := by
    apply LeftTangentOperator.commute_of_tangentMatrix_commute n dn ds
    rw [hdn, hds]
    exact hcomm
  have hsumOp : leftTangentOperator da =
      leftTangentOperator dn + leftTangentOperator ds := by
    rw [hsumDer, leftTangentOperator_add]
  have hlocal (a : TauCeti.GeneralLinear.coordinateHopfAlgebra K n) :
      ∃ W : Submodule K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n),
        ∃ _ : FiniteDimensional K W,
          ∃ hnW : W ∈ (leftTangentOperator dn).invtSubmodule,
            ∃ hsW : W ∈ (leftTangentOperator ds).invtSubmodule,
              a ∈ W ∧ IsNilpotent ((leftTangentOperator dn).restrict hnW) ∧
                Module.End.IsSemisimple ((leftTangentOperator ds).restrict hsW) := by
    obtain ⟨r, bound, ha⟩ := glCoordinateTruncation_exhaustive (K := K) n a
    let W := glCoordinateTruncation (K := K) n r bound
    have hfin : FiniteDimensional K W := glCoordinateTruncation_finite n r bound
    have hnW : W ∈ (leftTangentOperator dn).invtSubmodule := by
      intro b hb
      exact LeftTangentOperator.preserves_glCoordinateTruncation n dn r bound b hb
    have hsW : W ∈ (leftTangentOperator ds).invtSubmodule := by
      intro b hb
      exact LeftTangentOperator.preserves_glCoordinateTruncation n ds r bound b hb
    refine ⟨W, hfin, hnW, hsW, ha, ?_, ?_⟩
    · exact GlCoordinate.leftTangent_restrict_isNilpotent n dn
        (by rw [hdn]; exact hn) W hnW
    · exact hsfinite r bound
  simpa [dn, ds] using TangentJordanKernel.mem_range_of_finite_jordan_restrictions
    ρ hρ da dn ds ⟨d, rfl⟩ hcommOp hsumOp hlocal

omit [PerfectField K] in
private theorem tangentJordanLifts
    (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (Xn Xs : Matrix (Fin n) (Fin n) K)
    (hadd : Xn + Xs = TauCeti.GeneralLinear.tangentMatrix n
      (TauCeti.derivationComp (B := K) ρ d))
    (hparts : (TauCeti.GeneralLinear.tangentLinearEquivMatrix
      (R := K) (B := K) n).symm Xn ∈
        (TauCeti.derivationCompLieHom (B := K) ρ).range ∧
      (TauCeti.GeneralLinear.tangentLinearEquivMatrix
      (R := K) (B := K) n).symm Xs ∈
        (TauCeti.derivationCompLieHom (B := K) ρ).range) :
    ∃ dn ds : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K),
      TauCeti.derivationComp (B := K) ρ dn =
        (TauCeti.GeneralLinear.tangentLinearEquivMatrix
          (R := K) (B := K) n).symm Xn ∧
      TauCeti.derivationComp (B := K) ρ ds =
        (TauCeti.GeneralLinear.tangentLinearEquivMatrix
          (R := K) (B := K) n).symm Xs ∧
      dn + ds = d := by
  obtain ⟨dn, hn⟩ := hparts.1
  obtain ⟨ds, hs⟩ := hparts.2
  refine ⟨dn, ds, ?_, ?_, ?_⟩
  · exact hn
  · exact hs
  · apply TauCeti.derivationComp_injective_of_surjective ρ hρ
    have hn' : TauCeti.derivationComp (B := K) ρ dn =
        (TauCeti.GeneralLinear.tangentLinearEquivMatrix
          (R := K) (B := K) n).symm Xn := by
      exact hn
    have hs' : TauCeti.derivationComp (B := K) ρ ds =
        (TauCeti.GeneralLinear.tangentLinearEquivMatrix
          (R := K) (B := K) n).symm Xs := by
      exact hs
    apply (TauCeti.GeneralLinear.tangentLinearEquivMatrix
      (R := K) (B := K) n).injective
    rw [map_add, hn', hs', map_add,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      TauCeti.GeneralLinear.tangentLinearEquivMatrix_apply]
    exact hadd

/-- A commuting nilpotent and semisimple matrix decomposition of an
original-group tangent descends to two original-group tangents. -/
theorem algebraicTangentJordan
    [IsAlgClosed K]
    (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (Xn Xs : Matrix (Fin n) (Fin n) K)
    (hadd : Xn + Xs = TauCeti.GeneralLinear.tangentMatrix n
      (TauCeti.derivationComp (B := K) ρ d))
    (hcomm : Commute Xn Xs)
    (hn : IsNilpotent Xn)
    (hs : Module.End.IsSemisimple (Matrix.toLin' Xs)) :
    ∃ dn ds : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K),
      TauCeti.derivationComp (B := K) ρ dn =
        (TauCeti.GeneralLinear.tangentLinearEquivMatrix
          (R := K) (B := K) n).symm Xn ∧
      TauCeti.derivationComp (B := K) ρ ds =
        (TauCeti.GeneralLinear.tangentLinearEquivMatrix
          (R := K) (B := K) n).symm Xs ∧
      dn + ds = d := by
  have hsfinite : ∀ r bound : ℕ,
      let ds := (TauCeti.GeneralLinear.tangentLinearEquivMatrix
        (R := K) (B := K) n).symm Xs
      let W := glCoordinateTruncation (K := K) n r bound
      let hW : W ∈ (leftTangentOperator ds).invtSubmodule := by
        intro b hb
        exact LeftTangentOperator.preserves_glCoordinateTruncation n ds r bound b hb
      Module.End.IsSemisimple ((leftTangentOperator ds).restrict hW) := by
    intro r bound
    let ds := (TauCeti.GeneralLinear.tangentLinearEquivMatrix
      (R := K) (B := K) n).symm Xs
    have hds : TauCeti.GeneralLinear.tangentMatrix n ds = Xs := by
      rw [← TauCeti.GeneralLinear.tangentLinearEquivMatrix_apply]
      exact (TauCeti.GeneralLinear.tangentLinearEquivMatrix
        (R := K) (B := K) n).apply_symm_apply Xs
    have hsem : Module.End.IsSemisimple (leftTangentOperator ds) := by
      apply leftTangentOperator_isSemisimple n ds
      rw [hds]
      exact hs
    exact hsem.restrict _
  exact tangentJordanLifts n ρ hρ d Xn Xs hadd
    (AlgebraicTangentJordan.of_semisimple_restrictions
      n ρ hρ d Xn Xs hadd hcomm hn hsfinite)

end ReductiveGroups
