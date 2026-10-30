import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaCoefficientConvolution
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPoints
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Ga Closed Immersion

A nontrivial homomorphism from the additive group in characteristic zero
is a closed immersion at the level of coordinate algebras. -/

noncomputable section
namespace ReductiveGroups
open scoped TensorProduct

variable {K : Type*} [Field K] [CharZero K]

private def contractRight {A B : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (f : B →ₗ[K] K) :
    A ⊗[K] B →ₗ[K] A :=
  (TensorProduct.rid K A).toLinearMap.comp (f.lTensor A)

omit [CharZero K] in
private theorem contractRight_tmul {A B : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (f : B →ₗ[K] K) (a : A) (b : B) :
    contractRight f (a ⊗ₜ[K] b) = f b • a := rfl

omit [CharZero K] in
private theorem contractRight_map
    {A B : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (φ : A →ₗ[K] B) (f : B →ₗ[K] K)
    (x : A ⊗[K] A) :
    contractRight f (TensorProduct.map φ φ x) =
      φ (contractRight (f.comp φ) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [contractRight_tmul]
  | add x y hx hy => simp [hx, hy]

omit [CharZero K] in
private theorem gaContractRight_generator_pow (m d : ℕ) :
    contractRight (gaCoefficientLinear K m)
      (Coalgebra.comul (R := K) ((SymmetricAlgebra.ι K K 1) ^ d)) =
      (d.choose m : K) • (SymmetricAlgebra.ι K K 1) ^ (d - m) := by
  rw [Bialgebra.comul_pow, SymmetricAlgebra.comul_ι, add_pow]
  simp only [map_sum, ← nsmul_eq_mul', map_nsmul,
    Algebra.TensorProduct.tmul_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    contractRight_tmul, gaCoefficientLinear_apply,
    map_pow, gaPolynomialEquiv_generator, Polynomial.coeff_X_pow]
  by_cases hmd : m ≤ d
  · rw [Finset.sum_eq_single (d - m)]
    · simp [Nat.sub_sub_self hmd, Nat.choose_symm hmd, Algebra.smul_def]
    · intro x hx hne
      have hxd : x ≤ d := by simpa [Finset.mem_range] using hx
      have hmx : m ≠ d - x := by
        intro he
        omega
      simp [hmx]
    · simp [Finset.mem_range]
  · have hdm : d < m := by omega
    rw [Nat.choose_eq_zero_of_lt hdm, Nat.cast_zero, zero_smul]
    apply Finset.sum_eq_zero
    intro x hx
    have hmx : m ≠ d - x := by omega
    simp [hmx]

omit [CharZero K] in
private theorem gaContractRight_hasseDeriv (m : ℕ) (a : SymmetricAlgebra K K) :
    gaPolynomialEquiv K
      (contractRight (gaCoefficientLinear K m) (Coalgebra.comul (R := K) a)) =
      Polynomial.hasseDeriv m (gaPolynomialEquiv K a) := by
  obtain ⟨p, rfl⟩ := (gaPolynomialEquiv K).symm.surjective a
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ HAdd.hAdd hp hq
  | monomial d r =>
      have hpre : (gaPolynomialEquiv K).symm (Polynomial.monomial d r) =
          r • (SymmetricAlgebra.ι K K 1) ^ d := by
        apply (gaPolynomialEquiv K).injective
        simp only [AlgEquiv.apply_symm_apply, map_smul, map_pow,
          gaPolynomialEquiv_generator]
        rw [Polynomial.smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
      rw [hpre]
      simp only [map_smul, gaContractRight_generator_pow, map_pow,
        gaPolynomialEquiv_generator,
        Polynomial.smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
      simp [mul_comm]

private def gaHassePreimage {B : Type*} [CommRing B] [Bialgebra K B]
    (φ : B →ₐc[K] SymmetricAlgebra K K) (m : ℕ) (b : B) : B :=
  contractRight ((gaCoefficientLinear K m).comp φ.toAlgHom.toLinearMap)
    (Coalgebra.comul (R := K) b)

omit [CharZero K] in
private theorem gaHassePreimage_image {B : Type*} [CommRing B] [Bialgebra K B]
    (φ : B →ₐc[K] SymmetricAlgebra K K) (m : ℕ) (b : B) :
    gaPolynomialEquiv K (φ (gaHassePreimage φ m b)) =
      Polynomial.hasseDeriv m (gaPolynomialEquiv K (φ b)) := by
  have hc := congrArg (fun h : B →ₐ[K]
      (SymmetricAlgebra K K ⊗[K] SymmetricAlgebra K K) => h b)
    (BialgHom.map_comp_comulAlgHom φ)
  have hmap := contractRight_map φ.toAlgHom.toLinearMap
    (gaCoefficientLinear K m) (Coalgebra.comul (R := K) b)
  change contractRight (gaCoefficientLinear K m)
      (TensorProduct.map φ.toAlgHom.toLinearMap φ.toAlgHom.toLinearMap
        (Coalgebra.comul (R := K) b)) =
      φ (gaHassePreimage φ m b) at hmap
  rw [← hmap]
  have hc' : TensorProduct.map φ.toAlgHom.toLinearMap φ.toAlgHom.toLinearMap
      (Coalgebra.comul (R := K) b) = Coalgebra.comul (R := K) (φ b) := by
    have heq : (Algebra.TensorProduct.map φ φ).toLinearMap =
        TensorProduct.map φ.toAlgHom.toLinearMap φ.toAlgHom.toLinearMap := by
      ext a c
      simp
    rw [← heq]
    simpa only [AlgHom.toLinearMap_apply, AlgHom.comp_apply,
      Bialgebra.comulAlgHom_apply, BialgHom.coe_toAlgHom] using hc
  rw [hc']
  exact gaContractRight_hasseDeriv m (φ b)

/-- A nonzero-tangent additive subgroup is a closed immersion on
coordinate algebras. The nonzero tangent, rather than a surjectivity premise,
is the input. -/
theorem gaMorphism_surjective_of_tangent_ne_zero
    {B : Type*} [CommRing B] [HopfAlgebra K B]
    (φ : B →ₐc[K] SymmetricAlgebra K K)
    (hφ : gaAffineGroupTangent φ ≠ 0) : Function.Surjective φ := by
  let ψ : B →ₐ[K] Polynomial K :=
    (gaPolynomialEquiv K).toAlgHom.comp φ.toAlgHom
  have hex : ∃ b : B, (ψ b).coeff 1 ≠ 0 := by
    by_contra h
    have hz (b : B) : (ψ b).coeff 1 = 0 := by
      exact not_not.mp (not_exists.mp h b)
    apply hφ
    apply Derivation.ext
    intro b
    apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K).injective
    change TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K
      (TauCeti.derivationComp (B := K) φ (gaOriginDerivation K) b) = 0
    rw [gaOriginDerivation_comp_apply]
    exact hz b
  obtain ⟨b, hb⟩ := hex
  let p : Polynomial K := ψ b
  let d := p.natDegree
  have hd : 1 ≤ d := Polynomial.le_natDegree_of_ne_zero hb
  let q : Polynomial K := Polynomial.hasseDeriv (d - 1) p
  have hqdeg : q.natDegree = 1 := by
    simp [q, d, Polynomial.natDegree_hasseDeriv]
    omega
  have hq0 : q ≠ 0 := by
    intro h
    simp [h] at hqdeg
  have hq1 : q.coeff 1 ≠ 0 := by
    rw [← hqdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq0
  let c : B := gaHassePreimage φ (d - 1) b
  have hc : ψ c = q := gaHassePreimage_image φ (d - 1) b
  have hX : ∃ x : B, ψ x = Polynomial.X := by
    refine ⟨(algebraMap K B (q.coeff 1)⁻¹) *
      (c - algebraMap K B (q.coeff 0)), ?_⟩
    simp only [map_mul, map_sub, ψ.commutes, hc]
    have hqsub : q - Polynomial.C (q.coeff 0) =
        Polynomial.C (q.coeff 1) * Polynomial.X := by
      nth_rewrite 1 [q.eq_X_add_C_of_natDegree_le_one hqdeg.le]
      simp
    change Polynomial.C (q.coeff 1)⁻¹ *
      (q - Polynomial.C (q.coeff 0)) = Polynomial.X
    rw [hqsub]
    rw [← mul_assoc, ← map_mul]
    simp [hq1]
  obtain ⟨x, hx⟩ := hX
  have hψ : Function.Surjective ψ := by
    intro f
    induction f using Polynomial.induction_on' with
    | add f g hf hg =>
        obtain ⟨u, hu⟩ := hf
        obtain ⟨v, hv⟩ := hg
        exact ⟨u + v, by simp [hu, hv]⟩
    | monomial n r =>
        refine ⟨algebraMap K B r * x ^ n, ?_⟩
        simp [hx, Polynomial.C_mul_X_pow_eq_monomial]
  intro a
  obtain ⟨u, hu⟩ := hψ (gaPolynomialEquiv K a)
  refine ⟨u, (gaPolynomialEquiv K).injective ?_⟩
  exact hu

end ReductiveGroups
