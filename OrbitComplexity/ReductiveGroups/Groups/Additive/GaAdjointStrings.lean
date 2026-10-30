import OrbitComplexity.ReductiveGroups.Groups.Additive.GaSl2Reflection

/-! # First-order additive adjoint strings -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra
universe u v
section Lie
variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]

private theorem adjoint_exp_scaled (x : L)
    (hx : IsNilpotent (ad K L x)) (t : K) :
    nilpotentLieAdjointExponential (K := K) x hx t =
      nilpotentAdjointExponential (K := K) (t • x) (by simpa using hx.smul t) := rfl

private theorem exp_ad_first_order (x v : L) (hx : IsNilpotent (ad K L x))
    (hv : ⁅x, ⁅x, v⁆⁆ = 0) : nilpotentAdjointExponential (K := K) x hx v = v + ⁅x, v⁆ := by
  let : Module ℚ L := Module.compHom L (algebraMap ℚ K)
  let : Module ℚ (Module.End K L) := Module.compHom (Module.End K L) (algebraMap ℚ K)
  have hp : ((ad K L x) ^ 2) v = 0 := by
    simpa [Module.End.pow_apply] using hv
  unfold nilpotentAdjointExponential
  simp only [LieDerivation.exp_map_apply]
  have heq : ((LieDerivation.ad K L x).toLinearMap) = ad K L x := by
    ext y
    simp
  rw [heq]
  have hps : ((ad K L x) ^ 2) • v = 0 := by
    simpa only [Module.End.smul_def] using hp
  have he := IsNilpotent.exp_smul_eq_sum hps hx
  simp only [Module.End.smul_def] at he
  simpa [Finset.sum_range_succ, Module.End.smul_def] using he

private theorem lie_exp_first_order (x : L) (hx : IsNilpotent (ad K L x))
    (t : K) (z : L) (hz : ⁅x, ⁅x, z⁆⁆ = 0) :
    nilpotentLieAdjointExponential x hx t z = z + t • ⁅x, z⁆ := by
  rw [adjoint_exp_scaled]
  rw [exp_ad_first_order _ _ _ (by simp only [smul_lie, lie_smul, hz, smul_zero])]
  rw [smul_lie]

private theorem lower_exp_string (e f z : L)
    (he : IsNilpotent (ad K L e)) (hf : IsNilpotent (ad K L f))
    (a : K) (ha : a * a = 1) (hfz : ⁅f, z⁆ = 0)
    (heez : ⁅e, ⁅e, z⁆⁆ = 0) (hfez : ⁅f, ⁅e, z⁆⁆ = z) :
    nilpotentLieAdjointExponential e he a
      (nilpotentLieAdjointExponential f hf (-a)
        (nilpotentLieAdjointExponential e he a z)) = a • ⁅e, z⁆ := by
  have h1 := lie_exp_first_order e he a z heez
  have h2 : nilpotentLieAdjointExponential f hf (-a) z = z := by
    simpa only [hfz, smul_zero, add_zero] using
      lie_exp_first_order f hf (-a) z (by rw [hfz, lie_zero])
  have h3 := lie_exp_first_order f hf (-a) ⁅e, z⁆ (by rw [hfez, hfz])
  rw [hfez] at h3
  have hm : z + a • (⁅e, z⁆ + (-a) • z) = a • ⁅e, z⁆ := by
    rw [smul_add, smul_smul, mul_neg, ha, neg_one_smul]
    abel
  rw [h1, map_add, map_smul, h2, h3, hm, map_smul]
  have h4 := lie_exp_first_order e he a ⁅e, z⁆ (by rw [heez, lie_zero])
  rw [heez, smul_zero, add_zero] at h4
  rw [h4]

private theorem upper_exp_string (e f z : L)
    (he : IsNilpotent (ad K L e)) (hf : IsNilpotent (ad K L f))
    (a : K) (ha : a * a = 1) (hez : ⁅e, z⁆ = 0)
    (hffz : ⁅f, ⁅f, z⁆⁆ = 0) (hefz : ⁅e, ⁅f, z⁆⁆ = z) :
    nilpotentLieAdjointExponential e he a
      (nilpotentLieAdjointExponential f hf (-a)
        (nilpotentLieAdjointExponential e he a z)) = -a • ⁅f, z⁆ := by
  have h1 : nilpotentLieAdjointExponential e he a z = z := by
    simpa only [hez, smul_zero, add_zero] using
      lie_exp_first_order e he a z (by rw [hez, lie_zero])
  have h2 := lie_exp_first_order f hf (-a) z hffz
  have h3 := lie_exp_first_order e he a ⁅f, z⁆ (by rw [hefz, hez])
  rw [hefz] at h3
  rw [h1, h2, map_add, map_smul, h1, h3, smul_add, smul_smul, neg_mul, ha,
    neg_one_smul]
  abel

end Lie
section Group
variable {K : Type u} {B : Type v} [Field K] [CharZero K] [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B]
local notation "T" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- A lower two-vector string transforms by its first raising bracket. -/
theorem gaSl2Product_adjoint_lower (x y : B →ₐc[K] SymmetricAlgebra K K)
    (z : T) (a : K) (ha : a * a = 1)
    (hfz : ⁅gaAffineGroupTangent y, z⁆ = 0)
    (heez : ⁅gaAffineGroupTangent x, ⁅gaAffineGroupTangent x, z⁆⁆ = 0)
    (hfez : ⁅gaAffineGroupTangent y, ⁅gaAffineGroupTangent x, z⁆⁆ = z) :
    affineGroupAdjointRepresentation
      (gaAffineGroupPoints x (Multiplicative.ofAdd a) *
        gaAffineGroupPoints y (Multiplicative.ofAdd (-a)) *
          gaAffineGroupPoints x (Multiplicative.ofAdd a)) z =
      a • ⁅gaAffineGroupTangent x, z⁆ := by
  simp only [map_mul, Module.End.mul_apply, affineGroupAdjointRepresentation_apply,
    gaAffineGroup_adjoint_eq_exponential]
  exact lower_exp_string (gaAffineGroupTangent x) (gaAffineGroupTangent y) z
    (gaAffineGroupTangent_ad_nilpotent x) (gaAffineGroupTangent_ad_nilpotent y)
    a ha hfz heez hfez

/-- An upper two-vector string transforms by the negative first lowering bracket. -/
theorem gaSl2Product_adjoint_upper (x y : B →ₐc[K] SymmetricAlgebra K K)
    (z : T) (a : K) (ha : a * a = 1)
    (hez : ⁅gaAffineGroupTangent x, z⁆ = 0)
    (hffz : ⁅gaAffineGroupTangent y, ⁅gaAffineGroupTangent y, z⁆⁆ = 0)
    (hefz : ⁅gaAffineGroupTangent x, ⁅gaAffineGroupTangent y, z⁆⁆ = z) :
    affineGroupAdjointRepresentation
      (gaAffineGroupPoints x (Multiplicative.ofAdd a) *
        gaAffineGroupPoints y (Multiplicative.ofAdd (-a)) *
          gaAffineGroupPoints x (Multiplicative.ofAdd a)) z =
      -a • ⁅gaAffineGroupTangent y, z⁆ := by
  simp only [map_mul, Module.End.mul_apply, affineGroupAdjointRepresentation_apply,
    gaAffineGroup_adjoint_eq_exponential]
  exact upper_exp_string (gaAffineGroupTangent x) (gaAffineGroupTangent y) z
    (gaAffineGroupTangent_ad_nilpotent x) (gaAffineGroupTangent_ad_nilpotent y)
    a ha hez hffz hefz

end Group
end ReductiveGroups
