import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap

/-!
# Tangent Convolution Powers

Convolution powers of a tangent derivation and their binomial Leibniz rule. -/

noncomputable section
namespace ReductiveGroups
open WithConv TensorProduct
open TauCeti

variable {K B : Type*} [Field K] [CharZero K] [CommRing B] [HopfAlgebra K B]

/-- The scalar value of the `n`th convolution power of the linear map underlying
a tangent derivation. -/
def tangentConvolutionPower
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (n : ℕ) (b : B) : K :=
  (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K)
    (((toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) ^ n).ofConv b)

omit [CharZero K] in
/-- The equality is

```lean
tangentConvolutionPower d 0 b = Coalgebra.counit b
```
-/
@[simp] theorem tangentConvolutionPower_zero
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) (b : B) :
    tangentConvolutionPower d 0 b = Coalgebra.counit b := by
  simp only [tangentConvolutionPower, pow_zero, LinearMap.convOne_apply]
  change (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K)
    (algebraMap K (TauCeti.Bialgebra.CounitAlgebra K B K) (Coalgebra.counit b)) = _
  simpa using (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_apply K B K
    ((algebraMap K (TauCeti.Bialgebra.CounitAlgebra K B K)) (Coalgebra.counit b)))

omit [CharZero K] in
/-- The equality is

```lean
tangentConvolutionPower d 1 b =
      (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K) (d b)
```
-/
@[simp] theorem tangentConvolutionPower_one
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) (b : B) :
    tangentConvolutionPower d 1 b =
      (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K) (d b) := by
  simp only [tangentConvolutionPower, pow_one]
  rfl

omit [CharZero K] in
private theorem tangentConvPower_comp_mul
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) (n : ℕ) :
    toConv ((((toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) ^ n).ofConv) ∘ₗ
      LinearMap.mul' K B) =
      (TauCeti.LinearMap.mulTensor (1 : WithConv (B →ₗ[K]
        TauCeti.Bialgebra.CounitAlgebra K B K))
          (toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) +
        TauCeti.LinearMap.mulTensor
          (toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K))
          (1 : WithConv (B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K))) ^ n := by
  let f := toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)
  let q := TauCeti.LinearMap.mulTensor
      (1 : WithConv (B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) f +
    TauCeti.LinearMap.mulTensor f
      (1 : WithConv (B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K))
  change toConv (((f ^ n).ofConv) ∘ₗ LinearMap.mul' K B) = q ^ n
  induction n with
  | zero =>
      apply WithConv.ofConv_injective
      apply TensorProduct.ext'
      intro a b
      simp [f, q, LinearMap.convOne_apply, mul_comm]
      rfl
  | succ n ih =>
      have h := LinearMap.convMul_comp_coalgHom_distrib
        (f ^ n) f (Bialgebra.mulCoalgHom K B)
      rw [show (Bialgebra.mulCoalgHom K B).toLinearMap =
        LinearMap.mul' K B from rfl] at h
      rw [pow_succ, h, WithConv.toConv_ofConv,
        Derivation.toConv_coe_comp_mul', ih, pow_succ]

omit [CharZero K] in
private theorem mulTensor_one_one :
    TauCeti.LinearMap.mulTensor
      (1 : WithConv (B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K))
      (1 : WithConv (B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) = 1 := by
  apply WithConv.ofConv_injective
  apply TensorProduct.ext'
  intro a b
  simp [LinearMap.convOne_apply, mul_comm]
  rfl

omit [CharZero K] in
private theorem mulTensor_one_pow
    (f : WithConv (B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) (n : ℕ) :
    (TauCeti.LinearMap.mulTensor
      (1 : WithConv (B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) f) ^ n =
      TauCeti.LinearMap.mulTensor
        (1 : WithConv (B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) (f ^ n) := by
  induction n with
  | zero => simpa using (mulTensor_one_one (K := K) (B := B)).symm
  | succ n ih =>
      rw [pow_succ, ih, TauCeti.LinearMap.mulTensor_convMul,
        one_mul, pow_succ]

omit [CharZero K] in
private theorem mulTensor_pow_one
    (f : WithConv (B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) (n : ℕ) :
    (TauCeti.LinearMap.mulTensor f
      (1 : WithConv (B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K))) ^ n =
      TauCeti.LinearMap.mulTensor (f ^ n)
        (1 : WithConv (B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) := by
  induction n with
  | zero => simpa using (mulTensor_one_one (K := K) (B := B)).symm
  | succ n ih =>
      rw [pow_succ, ih, TauCeti.LinearMap.mulTensor_convMul,
        one_mul, pow_succ]

omit [CharZero K] in
private theorem tangentConvPower_comp_mul_binomial
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) (n : ℕ) :
    toConv ((((toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) ^ n).ofConv) ∘ₗ
      LinearMap.mul' K B) =
      ∑ k ∈ Finset.range (n + 1),
        TauCeti.LinearMap.mulTensor
          ((toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) ^ k)
          ((toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) ^ (n - k)) *
            (n.choose k : WithConv (B ⊗[K] B →ₗ[K]
              TauCeti.Bialgebra.CounitAlgebra K B K)) := by
  let f := toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)
  let p := TauCeti.LinearMap.mulTensor f
    (1 : WithConv (B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K))
  let q := TauCeti.LinearMap.mulTensor
    (1 : WithConv (B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) f
  have hpq : Commute p q := by
    change p * q = q * p
    simp [p, q, TauCeti.LinearMap.mulTensor_convMul]
  rw [tangentConvPower_comp_mul, show _ = p + q from add_comm _ _,
    hpq.add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mulTensor_pow_one, mulTensor_one_pow,
    TauCeti.LinearMap.mulTensor_convMul, one_mul, mul_one]

omit [CharZero K] in
private theorem tangentPower_scalar
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (n : ℕ) (b : B) :
    tangentConvolutionPower d n b =
      ((toConv ((TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K).toLinearMap ∘ₗ
        (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K))) ^ n).ofConv b := by
  let e := TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K
  let f := toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)
  let g := toConv (e.toLinearMap ∘ₗ f.ofConv)
  have h (m : ℕ) : e.toLinearMap ∘ₗ (f ^ m).ofConv = (g ^ m).ofConv := by
    induction m with
    | zero =>
        ext b
        simp only [pow_zero, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.convOne_apply]
        simpa using (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_apply K B K
          ((algebraMap K (TauCeti.Bialgebra.CounitAlgebra K B K))
            (Coalgebra.counit b)))
    | succ m ih =>
        rw [pow_succ, pow_succ]
        have hh := LinearMap.algHom_comp_convMul_distrib e.toAlgHom (f ^ m) f
        have he : e.toAlgHom.toLinearMap = e.toLinearMap := rfl
        rw [he] at hh
        exact hh.trans (by rw [← WithConv.toConv_ofConv (g ^ m), ← ih])
  unfold tangentConvolutionPower
  exact congrArg (fun q : B →ₗ[K] K => q b) (h n)

omit [CharZero K] in
private theorem convPower_comp_bialgHom
    {A : Type*} [CommRing A] [HopfAlgebra K A]
    (ρ : A →ₐc[K] B)
    (f : WithConv (B →ₗ[K] K))
    (n : ℕ) :
    (f ^ n).ofConv ∘ₗ (ρ : A →ₗc[K] B).toLinearMap =
      (toConv (f.ofConv ∘ₗ (ρ : A →ₗc[K] B).toLinearMap) ^ n).ofConv := by
  induction n with
  | zero =>
      ext a
      simp only [pow_zero, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.convOne_apply]
      exact congrArg (algebraMap K K)
        (CoalgHomClass.counit_comp_apply ρ a)
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (LinearMap.convMul_comp_coalgHom_distrib
        (f ^ n) f (ρ : A →ₗc[K] B)).trans (by rw [ih])

omit [CharZero K] in
/-- Convolution powers of tangents commute with precomposition by the
bialgebra morphism. -/
theorem tangentConvolutionPower_comp
    {A : Type*} [CommRing A] [HopfAlgebra K A]
    (ρ : A →ₐc[K] B)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (n : ℕ) (a : A) :
    tangentConvolutionPower (TauCeti.derivationComp (B := K) ρ d) n a =
      tangentConvolutionPower d n (ρ a) := by
  let eA := TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K A K
  let eB := TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K
  let f := toConv (eB.toLinearMap ∘ₗ
    (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K))
  have hbase :
      toConv (eA.toLinearMap ∘ₗ
        ((TauCeti.derivationComp (B := K) ρ d :
          Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K)) :
            A →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K A K)) =
      toConv (f.ofConv ∘ₗ (ρ : A →ₗc[K] B).toLinearMap) := by
    apply WithConv.toConv_injective
    ext a
    change eA (TauCeti.derivationComp (B := K) ρ d a) = eB (d (ρ a))
    exact TauCeti.algEquivSelf_derivationComp_apply ρ d a
  rw [tangentPower_scalar, tangentPower_scalar]
  rw [hbase]
  exact (congrArg (fun g : A →ₗ[K] K => g a)
    (convPower_comp_bialgHom ρ f n)).symm

omit [CharZero K] in
private theorem convMul_natCast
    (q : WithConv (B ⊗[K] B →ₗ[K]
      TauCeti.Bialgebra.CounitAlgebra K B K)) (m : ℕ) :
    q * (m : WithConv (B ⊗[K] B →ₗ[K]
      TauCeti.Bialgebra.CounitAlgebra K B K)) = m • q := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.cast_succ, mul_add, mul_one, ih, succ_nsmul]

omit [CharZero K] in
/-- The binomial Leibniz formula for convolution powers of a tangent
derivation. -/
theorem tangentConvolutionPower_mul
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (n : ℕ) (a b : B) :
    tangentConvolutionPower d n (a * b) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : K) * tangentConvolutionPower d k a *
          tangentConvolutionPower d (n - k) b := by
  have h := congrArg (fun q : WithConv (B ⊗[K] B →ₗ[K]
      TauCeti.Bialgebra.CounitAlgebra K B K) =>
    (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K)
      (q.ofConv (a ⊗ₜ[K] b))) (tangentConvPower_comp_mul_binomial d n)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mul'_apply] at h
  have hterm (k : ℕ) :
      (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K)
        ((TauCeti.LinearMap.mulTensor
          ((toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) ^ k)
          ((toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) ^ (n - k)) *
            (n.choose k : WithConv (B ⊗[K] B →ₗ[K]
              TauCeti.Bialgebra.CounitAlgebra K B K))).ofConv (a ⊗ₜ[K] b)) =
        (n.choose k : K) * tangentConvolutionPower d k a *
          tangentConvolutionPower d (n - k) b := by
    rw [convMul_natCast]
    change (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K)
      ((n.choose k) •
        (TauCeti.LinearMap.mulTensor
          ((toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) ^ k)
          ((toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) ^ (n - k))).ofConv
            (a ⊗ₜ[K] b)) = _
    rw [map_nsmul, TauCeti.LinearMap.mulTensor_apply_tmul]
    simp only [tangentConvolutionPower, map_mul, nsmul_eq_mul]
    rw [mul_assoc]
  calc
    tangentConvolutionPower d n (a * b) =
        (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K)
          ((∑ k ∈ Finset.range (n + 1),
            TauCeti.LinearMap.mulTensor
              ((toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) ^ k)
              ((toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) ^ (n - k)) *
                (n.choose k : WithConv (B ⊗[K] B →ₗ[K]
                  TauCeti.Bialgebra.CounitAlgebra K B K))).ofConv (a ⊗ₜ[K] b)) := h
    _ = ∑ k ∈ Finset.range (n + 1),
          (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K)
            ((TauCeti.LinearMap.mulTensor
              ((toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) ^ k)
              ((toConv (d : B →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K B K)) ^ (n - k)) *
                (n.choose k : WithConv (B ⊗[K] B →ₗ[K]
                  TauCeti.Bialgebra.CounitAlgebra K B K))).ofConv (a ⊗ₜ[K] b)) := by
        simp [WithConv.ofConv_sum, map_sum]
    _ = _ := Finset.sum_congr rfl (fun k _ => hterm k)

end ReductiveGroups
