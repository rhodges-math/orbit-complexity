import OrbitComplexity.FrobeniusSplitting.Splittings.Cartier
import Mathlib.Algebra.Polynomial.Monic
import OrbitComplexity.FrobeniusSplitting.Splittings.Laurent

/-!
# Cartier trace under changes of coordinate

In one variable the Cartier trace commutes with translation. Scaling the coordinate introduces
the inverse Jacobian to the characteristic minus one. In reciprocal Laurent coordinates the
corresponding weight is the twice-top monomial. The inclusion of ordinary polynomials in
Laurent polynomials intertwines the two trace operators.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Section 1.3.
-/

namespace FrobeniusSplitting

variable {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p]

/-- The polynomial Cartier trace specialized to one variable. -/
noncomputable def univariateTrace (base : RingSplitting R p) :
    FrobeniusLinearMap (Polynomial R) p where
  toAddMonoidHom := (MvPolynomial.uniqueAlgEquiv R Unit).toAddMonoidHom.comp
    ((polynomialTrace base (expChar_pos R p)).toAddMonoidHom.comp
      (MvPolynomial.uniqueAlgEquiv R Unit).symm.toAddMonoidHom)
  map_pow_mul' a b := by
    change (MvPolynomial.uniqueAlgEquiv R Unit)
      (polynomialTrace base (expChar_pos R p)
        ((MvPolynomial.uniqueAlgEquiv R Unit).symm (a ^ p * b))) =
      a * (MvPolynomial.uniqueAlgEquiv R Unit)
        (polynomialTrace base (expChar_pos R p)
          ((MvPolynomial.uniqueAlgEquiv R Unit).symm b))
    rw [_root_.map_mul, _root_.map_pow, FrobeniusLinearMap.map_pow_mul,
      _root_.map_mul, AlgEquiv.apply_symm_apply]

/-- The univariate Cartier trace extracts coefficients in degree congruent to minus one. -/
theorem univariateTrace_coeff (base : RingSplitting R p) (f : Polynomial R) (n : ℕ) :
    (univariateTrace base f).coeff n = base (f.coeff (p * n + (p - 1))) := by
  change ((MvPolynomial.uniqueAlgEquiv R Unit)
    (polynomialTrace base (expChar_pos R p)
      ((MvPolynomial.uniqueAlgEquiv R Unit).symm f))).coeff n = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv, polynomialTrace_coeff,
    MvPolynomial.coeff_uniqueAlgEquiv_symm]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, traceDegree_apply]

private theorem trace_of_small_degree (base : RingSplitting R p) (f : Polynomial R)
    (hf : f.natDegree < p) :
    univariateTrace base f = Polynomial.C (base (f.coeff (p - 1))) := by
  ext n
  rw [univariateTrace_coeff]
  cases n with
  | zero => simp only [mul_zero, zero_add, Polynomial.coeff_C_zero]
  | succ n =>
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt, base.map_zero]
    · simp
    · have hp := expChar_pos R p
      nlinarith

private theorem trace_small_translate (base : RingSplitting R p) (a r : R) (n : ℕ)
    (hn : n < p) :
    univariateTrace base (Polynomial.C r * (Polynomial.X + Polynomial.C a) ^ n) =
      if n = p - 1 then Polynomial.C (base r) else 0 := by
  have hd : (Polynomial.C r * (Polynomial.X + Polynomial.C a) ^ n).natDegree < p := by
    apply lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _)
    apply lt_of_le_of_lt Polynomial.natDegree_pow_le
    have hq : (Polynomial.X + Polynomial.C a).natDegree ≤ 1 :=
      Polynomial.natDegree_add_le_of_degree_le Polynomial.natDegree_X_le (by simp)
    exact (Nat.mul_le_mul_left n hq).trans_lt (by simpa using hn)
  rw [trace_of_small_degree base _ hd, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  by_cases h : n = p - 1
  · simp [h]
  · have hlt : n < p - 1 := by omega
    simp [h, Nat.choose_eq_zero_of_lt hlt]

private theorem trace_power_decomposition (base : RingSplitting R p) (r : R)
    (q : Polynomial R) (n : ℕ) :
    univariateTrace base (Polynomial.C r * q ^ n) =
      q ^ (n / p) * univariateTrace base (Polynomial.C r * q ^ (n % p)) := by
  have heq : Polynomial.C r * q ^ n =
      (q ^ (n / p)) ^ p * (Polynomial.C r * q ^ (n % p)) := by
    rw [← pow_mul]
    calc
      Polynomial.C r * q ^ n = Polynomial.C r * q ^ (n / p * p + n % p) := by
        rw [Nat.mul_comm (n / p) p, Nat.div_add_mod]
      _ = _ := by rw [pow_add]; ac_rfl
  rw [heq, FrobeniusLinearMap.map_pow_mul]

/-- The univariate Cartier trace commutes with translation of the coordinate. -/
theorem univariateTrace_translate (base : RingSplitting R p) (a : R) (f : Polynomial R) :
    univariateTrace base (f.comp (Polynomial.X + Polynomial.C a)) =
      (univariateTrace base f).comp (Polynomial.X + Polynomial.C a) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    simp only [Polynomial.add_comp, FrobeniusLinearMap.map_add, hf, hg]
  | monomial n r =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp,
      Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
      trace_power_decomposition, trace_small_translate base a r _
        (Nat.mod_lt _ (expChar_pos R p)), trace_power_decomposition]
    have hzero := trace_small_translate base 0 r (n % p)
      (Nat.mod_lt _ (expChar_pos R p))
    simp only [Polynomial.C_0, add_zero] at hzero
    rw [hzero]
    split_ifs <;> simp only [Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.X_comp, mul_zero, Polynomial.zero_comp]

/-- Scaling the coordinate transforms Cartier trace by the inverse Jacobian weight. -/
theorem univariateTrace_scale (base : RingSplitting R p) (a : Rˣ) (f : Polynomial R) :
    univariateTrace base
      (Polynomial.C ((↑(a⁻¹) : R) ^ (p - 1)) * f.comp (Polynomial.C (a : R) * Polynomial.X)) =
      (univariateTrace base f).comp (Polynomial.C (a : R) * Polynomial.X) := by
  ext n
  rw [univariateTrace_coeff, Polynomial.coeff_C_mul,
    Polynomial.comp_C_mul_X_coeff, Polynomial.comp_C_mul_X_coeff, univariateTrace_coeff]
  have hw : (↑(a⁻¹) : R) ^ (p - 1) * (a : R) ^ (p * n + (p - 1)) =
      ((a : R) ^ n) ^ p := by
    rw [pow_add]
    calc
      _ = (a : R) ^ (p * n) * ((↑(a⁻¹) : R) * (a : R)) ^ (p - 1) := by
        rw [mul_pow]
        ring
      _ = (a : R) ^ (p * n) := by simp
      _ = _ := by rw [Nat.mul_comm p n, pow_mul]
  calc
    _ = base (((a : R) ^ n) ^ p * f.coeff (p * n + (p - 1))) := by
      congr 1
      calc
        _ = ((↑(a⁻¹) : R) ^ (p - 1) * (a : R) ^ (p * n + (p - 1))) *
            f.coeff (p * n + (p - 1)) := by ring
        _ = _ := by rw [hw]
    _ = _ := by rw [base.map_pow_mul, mul_comm]


end FrobeniusSplitting

namespace FrobeniusSplitting

variable {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p]

/-- The Cartier trace in a Laurent coordinate. -/
noncomputable def laurentTrace (base : RingSplitting R p) :
    FrobeniusLinearMap (LaurentPolynomial R) p where
  toAddMonoidHom :=
    { toFun := fun f ↦ base.laurent (LaurentPolynomial.T (1 - p) * f)
      map_zero' := by rw [mul_zero, RingSplitting.map_zero]
      map_add' f g := by rw [mul_add, RingSplitting.map_add] }
  map_pow_mul' a b := by
    change base.laurent (LaurentPolynomial.T (1 - p) * (a ^ p * b)) =
      a * base.laurent (LaurentPolynomial.T (1 - p) * b)
    rw [← mul_assoc, mul_comm _ (a ^ p), mul_assoc, RingSplitting.map_pow_mul]

/-- Laurent Cartier trace extracts coefficients at shifted multiples of the characteristic. -/
theorem laurentTrace_coeff (base : RingSplitting R p) (f : LaurentPolynomial R) (n : ℤ) :
    (laurentTrace base f).coeff n = base (f.coeff (p • n + (p - 1))) := by
  change (base.laurent (LaurentPolynomial.T (1 - p) * f)).coeff n = _
  rw [RingSplitting.laurent_coeff]
  change base ((AddMonoidAlgebra.single (1 - (p : ℤ)) (1 : R) * f).coeff (p • n)) = _
  rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  congr 2
  omega

/-- The Laurent Cartier trace has the reciprocal-coordinate transformation law. -/
theorem laurentTrace_invert (base : RingSplitting R p) (f : LaurentPolynomial R) :
    laurentTrace base (LaurentPolynomial.T (2 * (p - 1)) * LaurentPolynomial.invert f) =
      LaurentPolynomial.invert (laurentTrace base f) := by
  ext n
  rw [laurentTrace_coeff, LaurentPolynomial.invert_apply, laurentTrace_coeff]
  change base ((AddMonoidAlgebra.single (2 * ((p : ℤ) - 1)) (1 : R) *
    LaurentPolynomial.invert f).coeff (p • n + (p - 1))) = _
  rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, LaurentPolynomial.invert_apply]
  congr 2
  simp only [smul_neg]
  ring

/-- Weighting Laurent Cartier trace by the top monomial gives the Laurent splitting. -/
theorem laurentTrace_weight (base : RingSplitting R p) (f : LaurentPolynomial R) :
    laurentTrace base (LaurentPolynomial.T (p - 1) * f) = base.laurent f := by
  change base.laurent (LaurentPolynomial.T (1 - p) *
    (LaurentPolynomial.T (p - 1) * f)) = _
  rw [← mul_assoc, ← LaurentPolynomial.T_add]
  simp only [sub_add_sub_cancel, sub_self, LaurentPolynomial.T_zero, one_mul]

end FrobeniusSplitting

namespace FrobeniusSplitting

variable {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p]

private theorem trace_toLaurent_coeff_nat (f : Polynomial R) (n : ℕ) :
    f.toLaurent.coeff (n : ℤ) = f.coeff n := by
  change (Finsupp.mapDomain (fun n : ℕ ↦ (n : ℤ)) f.toFinsupp.coeff) (n : ℤ) = f.coeff n
  rw [Finsupp.mapDomain_apply_of_injective Nat.cast_injective]
  rfl

private theorem trace_toLaurent_coeff_neg (f : Polynomial R) (n : ℤ) (hn : n < 0) :
    f.toLaurent.coeff n = 0 := by
  change (Finsupp.mapDomain (fun n : ℕ ↦ (n : ℤ)) f.toFinsupp.coeff) n = 0
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨m, hm⟩
  rw [← hm] at hn
  exact (not_lt_of_ge (Int.natCast_nonneg m)) hn

/-- Inclusion of ordinary polynomials in Laurent polynomials commutes with Cartier trace. -/
theorem laurentTrace_toLaurent (base : RingSplitting R p) (f : Polynomial R) :
    laurentTrace base f.toLaurent = (univariateTrace base f).toLaurent := by
  ext n
  cases n with
  | ofNat n =>
    rw [laurentTrace_coeff]
    change base (f.toLaurent.coeff (p • (n : ℤ) + ((p : ℤ) - 1))) =
      (univariateTrace base f).toLaurent.coeff (n : ℤ)
    have hp : 1 ≤ p := expChar_pos R p
    have hcast : p • (n : ℤ) + ((p : ℤ) - 1) = ((p * n + (p - 1) : ℕ) : ℤ) := by
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp, Nat.cast_one]
    rw [hcast, trace_toLaurent_coeff_nat, trace_toLaurent_coeff_nat, univariateTrace_coeff]
  | negSucc n =>
    have hneg : p • Int.negSucc n + ((p : ℤ) - 1) < 0 := by
      have hle : Int.negSucc n ≤ -1 := by omega
      have hmul := mul_le_mul_of_nonneg_left hle (Int.natCast_nonneg p)
      simp only [mul_neg_one] at hmul
      change (p : ℤ) * Int.negSucc n + ((p : ℤ) - 1) < 0
      omega
    rw [laurentTrace_coeff, trace_toLaurent_coeff_neg f _ hneg,
      trace_toLaurent_coeff_neg (univariateTrace base f) _ (Int.negSucc_lt_zero n),
      base.map_zero]

end FrobeniusSplitting
