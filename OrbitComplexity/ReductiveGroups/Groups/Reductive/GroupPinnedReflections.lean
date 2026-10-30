import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupPinnedRoots
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSl2Relations
import TauCeti.Algebra.Lie.Weights.Chevalley.Automorphism

/-! # Simple representatives and a compatible Lie involution -/

noncomputable section

namespace ReductiveGroups

open LieAlgebra LieModule TauCeti

universe u v w
variable {K : Type u} {M : Type v} {N : Type w} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

omit [CharZero K] in
private theorem end_pow_natural (f : M →ₗ[K] N) (X : Module.End K M)
    (Y : Module.End K N) (h : ∀ v, f (X v) = Y (f v)) (n : ℕ) (v : M) :
    f ((X ^ n) v) = (Y ^ n) (f v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]

omit [CharZero K] in
private theorem end_exp_natural [Module ℚ M] [Module ℚ N]
    (f : M →ₗ[K] N) (X : Module.End K M) (Y : Module.End K N)
    (hX : IsNilpotent X) (hY : IsNilpotent Y)
    (h : ∀ v, f (X v) = Y (f v)) (v : M) :
    f (IsNilpotent.exp X v) = IsNilpotent.exp Y (f v) := by
  obtain ⟨a, ha⟩ := hX
  obtain ⟨b, hb⟩ := hY
  have ha' : X ^ max a b = 0 := pow_eq_zero_of_le (Nat.le_max_left a b) ha
  have hb' : Y ^ max a b = 0 := pow_eq_zero_of_le (Nat.le_max_right a b) hb
  rw [IsNilpotent.exp_eq_sum ha', IsNilpotent.exp_eq_sum hb']
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_rat_smul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [end_pow_natural f X Y h n v]

omit [CharZero K] in
private theorem end_scalar_nilpotent (X Y : Module.End K M) (t : K)
    (hY : IsNilpotent Y) (h : ∀ v, X v = t • Y v) : IsNilpotent X := by
  have hp : ∀ (n : ℕ) (v : M), (X ^ n) v = t ^ n • (Y ^ n) v := by
    intro n v
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ' X, pow_succ' Y, Module.End.mul_apply, Module.End.mul_apply,
        h, ih, map_smul, smul_smul, pow_succ']
  obtain ⟨n, hn⟩ := hY
  refine ⟨n, LinearMap.ext fun v => ?_⟩
  rw [hp, hn, LinearMap.zero_apply, smul_zero]

namespace ReductiveGroupData

variable [IsAlgClosed K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] in
private theorem ga_adjoint_exp
    (x : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K) (t : K) (v : G.tangent) :
    let : Module ℚ G.tangent := Module.compHom G.tangent (algebraMap ℚ K)
    affineGroupAdjointRepresentation (gaParameterPoint x t) v =
      (IsNilpotent.exp (ad K G.tangent (t • gaAffineGroupTangent x))) v := by
  let : Module ℚ G.tangent := Module.compHom G.tangent (algebraMap ℚ K)
  change affineGroupAdjointRepresentation
    (gaAffineGroupPoints x (Multiplicative.ofAdd t)) v = _
  rw [affineGroupAdjointRepresentation_apply, gaAffineGroup_adjoint_eq_exponential]
  unfold nilpotentLieAdjointExponential
  rw [LieDerivation.exp_map_apply]
  simp only [LieDerivation.coe_ad_apply_eq_ad_apply]
  rfl

omit [IsAlgClosed K] in
private theorem quotient_ga_exp
    (x : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hx : IsNilpotent (ad K G.centerQuotient
      (centerQuotientLieHom (K := K) (gaAffineGroupTangent x))))
    (t : K) (v : G.centerQuotient) :
    let : Module ℚ G.centerQuotient := Module.compHom G.centerQuotient (algebraMap ℚ K)
    centerQuotientEquiv (affineGroupAdjointLieEquiv (gaParameterPoint x t)) v =
      (IsNilpotent.exp (ad K G.centerQuotient
        (t • centerQuotientLieHom (K := K) (gaAffineGroupTangent x)))) v := by
  have hX : IsNilpotent (ad K G.tangent (t • gaAffineGroupTangent x)) := by
    apply end_scalar_nilpotent _ (ad K G.tangent (gaAffineGroupTangent x)) t
      (gaAffineGroupTangent_ad_nilpotent x)
    intro z
    exact smul_lie t (gaAffineGroupTangent x) z
  have hY : IsNilpotent (ad K G.centerQuotient
      (t • centerQuotientLieHom (K := K) (gaAffineGroupTangent x))) := by
    rw [map_smul]
    exact hx.smul t
  let : Module ℚ G.tangent := Module.compHom G.tangent (algebraMap ℚ K)
  let : Module ℚ G.centerQuotient := Module.compHom G.centerQuotient (algebraMap ℚ K)
  obtain ⟨z, rfl⟩ := centerQuotientLieHom_surjective (K := K) (L := G.tangent) v
  rw [centerQuotientEquiv_apply, affineGroupAdjointLieEquiv_apply, ga_adjoint_exp G]
  exact end_exp_natural (centerQuotientLieHom (K := K)).toLinearMap _ _ hX hY
    (fun y => by
      change centerQuotientLieHom (K := K) ⁅t • gaAffineGroupTangent x, y⁆ =
        ⁅t • centerQuotientLieHom (K := K) (gaAffineGroupTangent x),
          centerQuotientLieHom (K := K) y⁆
      rw [LieHom.map_lie, map_smul]) z

omit [CharZero K] [IsAlgClosed K] in
private theorem quotient_adj_mul (p q : G.points) (v : G.centerQuotient) :
    centerQuotientEquiv (affineGroupAdjointLieEquiv (p * q)) v =
      centerQuotientEquiv (affineGroupAdjointLieEquiv p)
        (centerQuotientEquiv (affineGroupAdjointLieEquiv q) v) := by
  obtain ⟨z, rfl⟩ := centerQuotientLieHom_surjective (K := K) (L := G.tangent) v
  simp only [centerQuotientEquiv_apply, affineGroupAdjointLieEquiv_apply,
    map_mul, Module.End.mul_apply]

omit [IsAlgClosed K] in
private theorem quotient_ga_swap (ω : G.centerQuotient ≃ₗ⁅K⁆ G.centerQuotient)
    (x y : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hx : IsNilpotent (ad K G.centerQuotient
      (centerQuotientLieHom (K := K) (gaAffineGroupTangent x))))
    (hy : IsNilpotent (ad K G.centerQuotient
      (centerQuotientLieHom (K := K) (gaAffineGroupTangent y))))
    (hxy : ω (centerQuotientLieHom (K := K) (gaAffineGroupTangent x)) =
      -centerQuotientLieHom (K := K) (gaAffineGroupTangent y))
    (t : K) (v : G.centerQuotient) :
    ω (centerQuotientEquiv (affineGroupAdjointLieEquiv (gaParameterPoint x t)) v) =
      centerQuotientEquiv (affineGroupAdjointLieEquiv (gaParameterPoint y (-t))) (ω v) := by
  let : Module ℚ G.centerQuotient := Module.compHom G.centerQuotient (algebraMap ℚ K)
  rw [quotient_ga_exp G x hx, quotient_ga_exp G y hy]
  apply end_exp_natural ω.toLinearMap
  · rw [map_smul]
    exact hx.smul t
  · rw [map_smul]
    exact hy.smul (-t)
  · intro z
    change ω ⁅t • centerQuotientLieHom (K := K) (gaAffineGroupTangent x), z⁆ =
      ⁅(-t) • centerQuotientLieHom (K := K) (gaAffineGroupTangent y), ω z⁆
    rw [ω.map_lie, map_smul, hxy, smul_neg, neg_smul]

private theorem simple_commutes (ω : G.centerQuotient ≃ₗ⁅K⁆ G.centerQuotient)
    (i : G.rootBase.support)
    (hE : IsNilpotent (ad K G.centerQuotient
      (centerQuotientLieHom (K := K) (gaAffineGroupTangent (G.simpleRootMap i)))))
    (hF : IsNilpotent (ad K G.centerQuotient
      (centerQuotientLieHom (K := K) (gaAffineGroupTangent (G.negativeSimpleRootMap i)))))
    (he : ω (centerQuotientLieHom (K := K) (gaAffineGroupTangent (G.simpleRootMap i))) =
      -centerQuotientLieHom (K := K) (gaAffineGroupTangent (G.negativeSimpleRootMap i)))
    (hf : ω (centerQuotientLieHom (K := K)
      (gaAffineGroupTangent (G.negativeSimpleRootMap i))) =
        -centerQuotientLieHom (K := K) (gaAffineGroupTangent (G.simpleRootMap i)))
    (v : G.centerQuotient) :
    centerQuotientEquiv (affineGroupAdjointLieEquiv (G.reflectionPoint i.val)) (ω v) =
      ω (centerQuotientEquiv (affineGroupAdjointLieEquiv (G.reflectionPoint i.val)) v) := by
  have he' := quotient_ga_swap G ω (G.simpleRootMap i) (G.negativeSimpleRootMap i) hE hF he
  have hf' := quotient_ga_swap G ω (G.negativeSimpleRootMap i) (G.simpleRootMap i) hF hE hf
  have hn : G.reflectionPoint i.val =
      gaParameterPoint (G.simpleRootMap i) (1 : K) *
        gaParameterPoint (G.negativeSimpleRootMap i) (-1 : K) *
        gaParameterPoint (G.simpleRootMap i) (1 : K) := rfl
  have hswap : gaParameterPoint (G.simpleRootMap i) (1 : K) *
        gaParameterPoint (G.negativeSimpleRootMap i) (-1 : K) *
        gaParameterPoint (G.simpleRootMap i) (1 : K) =
      gaParameterPoint (G.negativeSimpleRootMap i) (-1 : K) *
        gaParameterPoint (G.simpleRootMap i) (1 : K) *
        gaParameterPoint (G.negativeSimpleRootMap i) (-1 : K) := G.simpleRoot_interchange i
  symm
  rw [hn]
  simp only [quotient_adj_mul, he', hf', neg_neg]
  simpa only [quotient_adj_mul] using congrArg
    (fun p : G.points => centerQuotientEquiv (affineGroupAdjointLieEquiv p) (ω v)) hswap.symm

/-- The chosen simple representatives commute with a compatible pinned Lie involution. -/
theorem exists_reflectionChevalleySystem :
    ∃ (ω : G.centerQuotient ≃ₗ⁅K⁆ G.centerQuotient)
      (x : LieModule.Weight K G.cartan G.centerQuotient → G.centerQuotient),
      IsChevalleySystem ω x ∧
      (∀ i : G.rootBase.support,
        x i.val.val = centerQuotientLieHom (K := K)
          (gaAffineGroupTangent (G.simpleRootMap i)) ∧
        x (-i.val.val) = centerQuotientLieHom (K := K)
          (gaAffineGroupTangent (G.negativeSimpleRootMap i))) ∧
      ∀ (i : G.rootBase.support) (v : G.centerQuotient),
        centerQuotientEquiv (affineGroupAdjointLieEquiv (G.reflectionPoint i.val)) (ω v) =
          ω (centerQuotientEquiv (affineGroupAdjointLieEquiv (G.reflectionPoint i.val)) v) := by
  obtain ⟨ω, x, hx, hi⟩ := G.exists_pinnedChevalleySystem
  refine ⟨ω, x, hx, hi, ?_⟩
  intro i v
  apply simple_commutes G ω i
  · rw [← (hi i).1]
    exact hx.toIsSl2System.isNilpotent_ad_rootVector i.val.val
  · rw [← (hi i).2]
    exact hx.toIsSl2System.isNilpotent_ad_rootVector (-i.val.val)
  · rw [← (hi i).1, hx.map_root, (hi i).2]
  · rw [← (hi i).2, hx.map_root, neg_neg, (hi i).1]

end ReductiveGroupData

end ReductiveGroups
