import OrbitComplexity.ReductiveGroups.Groups.Representations.GLCoordinateGenerators
import Mathlib.RingTheory.Derivation.Lie

/-!
# GL Coordinate Commutation

Commuting tangent matrices give commuting coordinate operators. The row
action reverses multiplication order; this statement does not use a Lie
algebra homomorphism. -/

noncomputable section
namespace ReductiveGroups

private theorem end_comp_row_action
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι]
    (f g : Module.End K V) (X Y : Matrix ι ι K) (v : ι → V)
    (hf : ∀ i, f (v i) = ∑ j, X i j • v j)
    (hg : ∀ i, g (v i) = ∑ j, Y i j • v j) (i : ι) :
    f (g (v i)) = ∑ j, (Y * X) i j • v j := by
  rw [hg]
  simp only [map_sum, map_smul, hf, Finset.smul_sum, smul_smul,
    Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

variable {K : Type*} [Field K] (n : ℕ)

/-- The coordinate operators commute whenever their tangent matrices
commute. This includes the pair of matrix Jordan components. -/
theorem LeftTangentOperator.commute_of_tangentMatrix_commute
    (d e : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K))
    (hc : Commute (TauCeti.GeneralLinear.tangentMatrix n d)
      (TauCeti.GeneralLinear.tangentMatrix n e)) :
    Commute (leftTangentOperator d) (leftTangentOperator e) := by
  have hb : ⁅leftTangentDerivation d, leftTangentDerivation e⁆ = 0 := by
    apply Derivation.ext_of_adjoin_eq_top _ (glCoordinate_adjoin_entries_detInverse n)
    intro a ha
    rcases ha with ⟨⟨i, j⟩, rfl⟩ | ha
    · change leftTangentOperator d
          (leftTangentOperator e (TauCeti.GeneralLinear.genericMatrix K n i j)) -
        leftTangentOperator e
          (leftTangentOperator d (TauCeti.GeneralLinear.genericMatrix K n i j)) = 0
      apply sub_eq_zero.mpr
      rw [end_comp_row_action (leftTangentOperator d) (leftTangentOperator e)
        (TauCeti.GeneralLinear.tangentMatrix n d) (TauCeti.GeneralLinear.tangentMatrix n e)
        (fun i => TauCeti.GeneralLinear.genericMatrix K n i j)
        (fun i => leftTangentOperator_genericMatrix_apply n d i j)
        (fun i => leftTangentOperator_genericMatrix_apply n e i j),
        end_comp_row_action (leftTangentOperator e) (leftTangentOperator d)
        (TauCeti.GeneralLinear.tangentMatrix n e) (TauCeti.GeneralLinear.tangentMatrix n d)
        (fun i => TauCeti.GeneralLinear.genericMatrix K n i j)
        (fun i => leftTangentOperator_genericMatrix_apply n e i j)
        (fun i => leftTangentOperator_genericMatrix_apply n d i j), hc.eq]
    · have heq : a = detInverseCoordinate (K := K) n := Set.mem_singleton_iff.mp ha
      subst a
      change leftTangentOperator d (leftTangentOperator e (detInverseCoordinate (K := K) n)) -
        leftTangentOperator e (leftTangentOperator d (detInverseCoordinate (K := K) n)) = 0
      rw [leftTangentOperator_detInverseCoordinate, leftTangentOperator_detInverseCoordinate]
      simp only [map_smul, leftTangentOperator_detInverseCoordinate, smul_smul]
      rw [mul_comm]
      exact sub_self _
  apply LinearMap.ext
  intro a
  have hz := DFunLike.congr_fun hb a
  change leftTangentOperator d (leftTangentOperator e a) -
    leftTangentOperator e (leftTangentOperator d a) = 0 at hz
  exact sub_eq_zero.mp hz

end ReductiveGroups
