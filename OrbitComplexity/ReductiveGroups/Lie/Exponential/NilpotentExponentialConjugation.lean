import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Nilpotent Exponential Conjugation

Conjugation by a finite exponential in a characteristic-zero associative algebra. -/

noncomputable section

namespace ReductiveGroups

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]


/-- The rational finite exponential by a characteristic-zero `K`-algebra. -/
def associativeExponential (x : A) : A := by
  letI : Algebra ℚ K := (Rat.castHom K).toAlgebra
  letI : Module ℚ A := Module.compHom A (algebraMap ℚ K)
  exact IsNilpotent.exp x

/-- The two finite exponentials used in conjugation are mutual inverses. -/
theorem associativeExponential_inverse {x : A} (hx : IsNilpotent x) :
    associativeExponential (K := K) x * associativeExponential (K := K) (-x) = 1 ∧
      associativeExponential (K := K) (-x) * associativeExponential (K := K) x = 1 :=
  letI : Algebra ℚ K := (Rat.castHom K).toAlgebra
  letI : Module ℚ A := Module.compHom A (algebraMap ℚ K)
  by
    constructor
    · exact IsNilpotent.exp_mul_exp_neg_self hx
    · exact IsNilpotent.exp_neg_mul_exp_self hx

/-- The commutator with `x`, viewed as a linear endomorphism. -/
def associativeAdjoint (x : A) : Module.End K A :=
  LinearMap.mulLeft K x - LinearMap.mulRight K x

omit [CharZero K] in
/-- The equality is

```lean
associativeAdjoint (K := K) x y = x * y - y * x
```
-/
@[simp] theorem associativeAdjoint_apply (x y : A) :
    associativeAdjoint (K := K) x y = x * y - y * x := rfl

omit [CharZero K] in
/-- The associative commutator agrees with Mathlib's adjoint for its standard Lie structure. -/
theorem associativeAdjoint_eq_ad (x : A) :
    associativeAdjoint (K := K) x = LieAlgebra.ad K A x := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  rfl

/-- The rational finite exponential of the commutator endomorphism. -/
def associativeAdjointExponential (x : A) : Module.End K A := by
  letI : Algebra ℚ K := (Rat.castHom K).toAlgebra
  letI : Module ℚ (Module.End K A) :=
    Module.compHom (Module.End K A) (algebraMap ℚ K)
  exact IsNilpotent.exp (associativeAdjoint (K := K) x)

omit [CharZero K] in
private theorem rightMul_pow_apply (x y : A) (n : ℕ) :
    ((LinearMap.mulRight K x) ^ n) y = y * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, LinearMap.mulRight_apply,
      ih, pow_succ, mul_assoc]

omit [CharZero K] in
private theorem rightMul_nilpotent {x : A} (hx : IsNilpotent x) :
    IsNilpotent (LinearMap.mulRight K x) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  ext y
  simp [hn]

private theorem rightMul_exp_apply {x : A} (hx : IsNilpotent x) (y : A) :
    (by
      letI : Algebra ℚ K := (Rat.castHom K).toAlgebra
      letI : Module ℚ (Module.End K A) :=
        Module.compHom (Module.End K A) (algebraMap ℚ K)
      exact IsNilpotent.exp (LinearMap.mulRight K x) : Module.End K A) y =
      y * associativeExponential (K := K) x :=
  letI : Algebra ℚ K := (Rat.castHom K).toAlgebra
  letI : Module ℚ A := Module.compHom A (algebraMap ℚ K)
  letI : Module ℚ (Module.End K A) :=
    Module.compHom (Module.End K A) (algebraMap ℚ K)
  by
    obtain ⟨n, hn⟩ := hx
    have hright : (LinearMap.mulRight K x) ^ n = 0 := by
      ext z
      simp [hn]
    change IsNilpotent.exp (LinearMap.mulRight K x) y = y * IsNilpotent.exp x
    rw [IsNilpotent.exp_eq_sum hright, IsNilpotent.exp_eq_sum hn]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, rightMul_pow_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    change (algebraMap ℚ K ((j.factorial : ℚ)⁻¹)) • (y * x ^ j) =
      y * ((algebraMap ℚ K ((j.factorial : ℚ)⁻¹)) • x ^ j)
    exact (mul_smul_comm _ _ _).symm

omit [CharZero K] in
private theorem leftRight_commute (x : A) :
    Commute (LinearMap.mulLeft K x) (LinearMap.mulRight K x) := by
  ext y
  simp [mul_assoc]

omit [CharZero K] in
/-- A nilpotent algebra element has nilpotent commutator action. -/
theorem associativeAdjoint_nilpotent {x : A} (hx : IsNilpotent x) :
    IsNilpotent (associativeAdjoint (K := K) x) := by
  exact (leftRight_commute (K := K) x).isNilpotent_sub
    (hx.map (Algebra.lmul K A)) (rightMul_nilpotent (K := K) hx)

/-- The finite exponential of the commutator acts by algebra conjugation. -/
theorem associativeAdjoint_exp_apply {x : A} (hx : IsNilpotent x) (y : A) :
    associativeAdjointExponential (K := K) x y =
      associativeExponential (K := K) x * y *
        associativeExponential (K := K) (-x) :=
  letI : Algebra ℚ K := (Rat.castHom K).toAlgebra
  letI : Module ℚ A := Module.compHom A (algebraMap ℚ K)
  letI : Module ℚ (Module.End K A) :=
    Module.compHom (Module.End K A) (algebraMap ℚ K)
  by
    let L : Module.End K A := LinearMap.mulLeft K x
    let R : Module.End K A := LinearMap.mulRight K x
    have hL : IsNilpotent L := hx.map (Algebra.lmul K A)
    have hR : IsNilpotent R := rightMul_nilpotent (K := K) hx
    have hLR : Commute L R := leftRight_commute (K := K) x
    have hLexp : IsNilpotent.exp L = LinearMap.mulLeft K (IsNilpotent.exp x) := by
      exact (hx.map_exp (Algebra.lmul K A)).symm
    have hRexp (z : A) : IsNilpotent.exp (-R) z = z * IsNilpotent.exp (-x) := by
      have hneg : -R = LinearMap.mulRight K (-x) := by
        ext w
        simp [R]
      rw [hneg]
      simpa [associativeExponential] using rightMul_exp_apply (K := K) hx.neg z
    change IsNilpotent.exp (L - R) y = IsNilpotent.exp x * y * IsNilpotent.exp (-x)
    rw [sub_eq_add_neg, IsNilpotent.exp_add_of_commute (hLR.neg_right) hL hR.neg]
    simp [hLexp, hRexp, mul_assoc]

end ReductiveGroups
