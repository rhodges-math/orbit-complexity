import OrbitComplexity.ReductiveGroups.Lie.Basis.OppositeSigns
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupPinnedParameters
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPointInjectivity

/-! # Tangent coefficients of root-parameter conjugation -/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open LieAlgebra LieModule TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem tangent_coefficient
    (s : G.rootIndex) (φ ψ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hψ : gaAffineGroupTangent ψ ∈ G.rootWeightSpace s)
    (hψn : gaAffineGroupTangent ψ ≠ 0) (p : G.points) (ε : K)
    (hm : affineGroupAdjointRepresentation p (gaAffineGroupTangent φ) ∈
      G.rootWeightSpace s)
    (he : ∀ a : K, p * gaParameterPoint φ a * p⁻¹ = gaParameterPoint ψ (ε * a)) :
    affineGroupAdjointRepresentation p (gaAffineGroupTangent φ) =
      ε • gaAffineGroupTangent ψ := by
  have hn : (⟨gaAffineGroupTangent ψ, hψ⟩ : G.rootWeightSpace s) ≠ 0 := by
    intro h
    exact hψn (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hn).mp
    (G.rootWeightSpace_finrank s)
    (⟨affineGroupAdjointRepresentation p (gaAffineGroupTangent φ), hm⟩ :
      G.rootWeightSpace s)
  have ht : affineGroupAdjointRepresentation p (gaAffineGroupTangent φ) =
      c • gaAffineGroupTangent ψ := (congrArg Subtype.val hc).symm
  have hp : p * gaParameterPoint φ (1 : K) * p⁻¹ = gaParameterPoint ψ c := by
    simpa only [gaParameterPoint, gaAffineGroupPoints, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, mul_one] using
      GaAffineGroupPoints.conjugate_of_tangent_eq φ ψ p c ht 1
  have hcε : c = ε := by
    have heq : gaParameterPoint ψ c = gaParameterPoint ψ ε := by
      rw [← hp]
      simpa only [mul_one] using he 1
    exact congrArg Multiplicative.toAdd
      (GaAffineGroupPoints.injective_of_tangent_ne_zero ψ hψn heq)
  simpa only [hcε] using ht

/-- Conjugation coefficients of opposite normalized root parameters agree. -/
theorem root_parameter_signs_equal
    (x : Weight K G.cartan G.centerQuotient → G.centerQuotient) (hx : IsSl2System x)
    (φ : G.rootIndex → G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hm : ∀ r, gaAffineGroupTangent (φ r) ∈ G.rootWeightSpace r)
    (hq : ∀ r, centerQuotientLieHom (K := K) (gaAffineGroupTangent (φ r)) = x r.val)
    (p : G.points) (τ : Equiv.Perm G.rootIndex) (hp : G.rootPointTransport p τ)
    (hneg : ∀ r, τ (-r) = -τ r) (r : G.rootIndex) (a b : K) (ha : a * a = 1)
    (he : ∀ t : K, p * gaParameterPoint (φ r) t * p⁻¹ =
      gaParameterPoint (φ (τ r)) (a * t))
    (hf : ∀ t : K, p * gaParameterPoint (φ (-r)) t * p⁻¹ =
      gaParameterPoint (φ (τ (-r))) (b * t)) : a = b := by
  have hn (s : G.rootIndex) : gaAffineGroupTangent (φ s) ≠ 0 := by
    intro hz
    have h := hq s
    rw [hz, map_zero] at h
    exact hx.ne_zero s.val (LieSubalgebra.isNonZero_coe_root s) h.symm
  have ht (s : G.rootIndex) :
      affineGroupAdjointRepresentation p (gaAffineGroupTangent (φ s)) ∈
        G.rootWeightSpace (τ s) := by
    rw [← hp s]
    exact ⟨gaAffineGroupTangent (φ s), hm s, rfl⟩
  have he' := tangent_coefficient G (τ r) (φ r) (φ (τ r)) (hm (τ r))
    (hn (τ r)) p a (ht r) he
  have hf' := tangent_coefficient G (τ (-r)) (φ (-r)) (φ (τ (-r)))
    (hm (τ (-r))) (hn (τ (-r))) p b (ht (-r)) hf
  let σ := centerQuotientEquiv (affineGroupAdjointLieEquiv p)
  have heq : σ (x r.val) = a • x (τ r).val := by
    rw [← hq r, centerQuotientEquiv_apply, affineGroupAdjointLieEquiv_apply,
      he', map_smul, hq]
  have hfq : σ (x (-r.val)) = b • x (-(τ r).val) := by
    change σ (x (-r).val) = b • x (-(τ r)).val
    rw [← hq (-r), centerQuotientEquiv_apply, affineGroupAdjointLieEquiv_apply,
      hf', map_smul, hq, hneg]
  exact ReductiveGroups.opposite_signs_equal hx σ r.val (τ r).val
    (LieSubalgebra.isNonZero_coe_root r) (LieSubalgebra.isNonZero_coe_root (τ r))
    a b ha heq hfq

end ReductiveGroups.ReductiveGroupData
