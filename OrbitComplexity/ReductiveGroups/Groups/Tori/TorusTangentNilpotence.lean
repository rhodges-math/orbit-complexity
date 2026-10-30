import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusMatrixInvariantSubspace

/-!
# Torus Tangent Nilpotence

Torus tangents have no nonzero nilpotent represented directions in a
faithful matrix representation. This follows directly from character weights. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

variable {K M V : Type*} [Field K] [CommGroup M]
  [AddCommGroup V] [Module K V] [Comodule K (MonoidAlgebra K M) V]

/-- A nilpotent differentiated torus action is zero: the character spaces
span and consist of eigenvectors, even without finite dimension. -/
theorem TorusTangentOperator.eq_zero_of_isNilpotent
    (h : Derivation K (MonoidAlgebra K M)
      (Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K))
    (hnil : IsNilpotent (torusTangentOperator (V := V) h)) :
    torusTangentOperator (V := V) h = 0 := by
  let f : Module.End K V := torusTangentOperator h
  obtain ⟨n, hn⟩ := hnil
  have hker : (⨆ α : M, Comodule.weightSpace K M V α) ≤ f.ker := by
    refine iSup_le fun α => ?_
    intro v hv
    have he : f v = characterDifferential α h • v := torusTangentOperator_weight h α hv
    have hp (m : ℕ) : (f ^ m) v = (characterDifferential α h) ^ m • v := by
      induction m with
      | zero => simp only [pow_zero, Module.End.one_apply, one_smul]
      | succ m hm =>
          rw [pow_succ, Module.End.mul_apply, he, map_smul, hm, smul_smul, pow_succ]
          rw [mul_comm]
    have hz : (characterDifferential α h) ^ n • v = 0 := by
      rw [← hp n]
      change (torusTangentOperator h ^ n) v = 0
      rw [hn, LinearMap.zero_apply]
    change f v = 0
    rw [he]
    rcases smul_eq_zero.mp hz with hscalar | hv0
    · rw [eq_zero_of_pow_eq_zero hscalar, zero_smul]
    · rw [hv0, smul_zero]
  rw [Comodule.iSup_weightSpace_eq_top] at hker
  exact LinearMap.ker_eq_top.mp (top_unique hker)

/-- A nilpotent matrix differential of a split-torus representation
vanishes. The representation need not be faithful for this matrix statement. -/
theorem TorusMatrixTangent.eq_zero_of_isNilpotent {ι : Type*} (n : ℕ)
    (q : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (h : Derivation K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
      (Bialgebra.CounitAlgebra K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K))
    (hnil : IsNilpotent (affineGroupMatrixDifferential n q h)) :
    affineGroupMatrixDifferential n q h = 0 := by
  let _ := torusMatrixComodule K n q
  have he := hnil.map (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
    Module.End K (Fin n → K)).toAlgHom
  have hnil' : IsNilpotent (torusTangentOperator (V := Fin n → K) h) := by
    rw [torusMatrixTangentOperator_eq_matrix K n q h]
    exact he
  have hz := TorusTangentOperator.eq_zero_of_isNilpotent h hnil'
  rw [torusMatrixTangentOperator_eq_matrix K n q h] at hz
  apply (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
    Module.End K (Fin n → K)).injective
  rw [map_zero]
  exact hz

variable {B : Type*} [CommRing B] [HopfAlgebra K B]

/-- A torus tangent represented nilpotently by a faithful
coordinate representation is zero in the original group tangent. -/
theorem TorusTangent.eq_zero_of_faithful_matrix_nilpotent {ι : Type*}
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (d : Derivation K B (Bialgebra.CounitAlgebra K B K))
    (hd : d ∈ diagonalizableTangentImage π)
    (hnil : IsNilpotent (affineGroupMatrixDifferential n ρ d)) : d = 0 := by
  obtain ⟨h, rfl⟩ := hd
  have he : affineGroupMatrixDifferential n (π.comp ρ) h =
      affineGroupMatrixDifferential n ρ ((derivationCompLieHom (B := K) π) h) := by
    simp only [affineGroupMatrixDifferential_apply, derivationComp_comp,
      LinearMap.comp_apply, derivationCompLieHom_apply]
  have hz := TorusMatrixTangent.eq_zero_of_isNilpotent n (π.comp ρ) h (he.symm ▸ hnil)
  rw [he] at hz
  apply AffineGroupMatrixDifferential.injective_of_surjective n ρ hρ
  rw [map_zero]
  exact hz

end ReductiveGroups
