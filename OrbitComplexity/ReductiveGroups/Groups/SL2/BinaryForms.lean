import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear substitutions on homogeneous binary forms

The degree-`n` monomials are ordered by the exponent of the second variable.
Column substitutions give a matrix representation in this basis.
-/

noncomputable section

namespace ReductiveGroups.BinaryForms

open Module MvPolynomial
open scoped Matrix

universe u v

/-- The exponent vector of `X₀^(n-j) X₁^j`. -/
def exponent (n : ℕ) (j : Fin (n + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) (n - (j : ℕ)) + Finsupp.single (1 : Fin 2) (j : ℕ)

private theorem exponent_degree (n : ℕ) (j : Fin (n + 1)) :
    (exponent n j).degree = n := by
  simp only [exponent, map_add, Finsupp.degree_single]
  omega

private def exponentEquiv (n : ℕ) :
    Fin (n + 1) ≃ {d : Fin 2 →₀ ℕ // d.degree = n} where
  toFun j := ⟨exponent n j, exponent_degree n j⟩
  invFun d := ⟨d.val 1, by have := Finsupp.le_degree 1 d.val; omega⟩
  left_inv j := by ext; simp [exponent]
  right_inv d := by
    apply Subtype.ext
    have hd : d.val 0 + d.val 1 = n := by
      simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using d.property
    ext i
    fin_cases i
    · simp [exponent]
      omega
    · simp [exponent]

private theorem exponent_injective (n : ℕ) : Function.Injective (exponent n) := by
  intro i j hij
  apply Fin.ext
  simpa [exponent] using congrArg (fun d : Fin 2 →₀ ℕ => d 1) hij

variable (R : Type u) [CommRing R]

private def monomialBasis (n : ℕ) :
    Basis {d : Fin 2 →₀ ℕ // d.degree = n} R (homogeneousSubmodule (Fin 2) R n) :=
  (basisRestrictSupport R {d : Fin 2 →₀ ℕ | d.degree = n}).map
    (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin 2) R n).symm)

private theorem monomialBasis_coe (n : ℕ) (d : {d : Fin 2 →₀ ℕ // d.degree = n}) :
    (monomialBasis R n d : MvPolynomial (Fin 2) R) = monomial d.val 1 := by
  classical
  change (((AddMonoidAlgebra.supportedEquivFinsupp (R := R) (S := R)
    {d : Fin 2 →₀ ℕ | d.degree = n}).symm (Finsupp.single d 1) :
      restrictSupport R {d : Fin 2 →₀ ℕ | d.degree = n}) : MvPolynomial (Fin 2) R) = _
  simp only [AddMonoidAlgebra.supportedEquivFinsupp, LinearEquiv.symm_trans_apply]
  simp [AddMonoidAlgebra.ofCoeff_single, single_eq_monomial]

/-- The monomial basis of homogeneous binary forms. -/
def basis (n : ℕ) : Basis (Fin (n + 1)) R (homogeneousSubmodule (Fin 2) R n) :=
  (monomialBasis R n).reindex (exponentEquiv n).symm

/-- A binary-form basis vector is its specified monomial. -/
theorem basis_coe (n : ℕ) (j : Fin (n + 1)) :
    (basis R n j : MvPolynomial (Fin 2) R) = monomial (exponent n j) 1 := by
  simp only [basis, Basis.reindex_apply, Equiv.symm_symm]
  exact monomialBasis_coe R n ((exponentEquiv n) j)

/-- A matrix substitutes its columns for the two variables. -/
def substitution (a : Matrix (Fin 2) (Fin 2) R) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval fun j => ∑ i, C (a i j) * X i

private theorem substitution_X (a : Matrix (Fin 2) (Fin 2) R) (j : Fin 2) :
    substitution R a (X j) = ∑ i, C (a i j) * X i :=
  aeval_X _ _

private theorem substitution_C (a : Matrix (Fin 2) (Fin 2) R) (r : R) :
    substitution R a (C r) = C r := by
  exact (substitution R a).commutes r

/-- Successive column substitutions multiply their matrices. -/
theorem substitution_mul (a b : Matrix (Fin 2) (Fin 2) R) :
    substitution R (a * b) = (substitution R a).comp (substitution R b) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, substitution_X, map_sum, map_mul, substitution_C]
  simp only [Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul, ← mul_assoc,
    ← map_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun k _ => by
      rw [mul_comm (a k i) (b i j)]

private theorem substitution_one :
    substitution R (1 : Matrix (Fin 2) (Fin 2) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [substitution_X, Matrix.one_apply]

private theorem substitution_homogeneous (n : ℕ) (a : Matrix (Fin 2) (Fin 2) R)
    {p : MvPolynomial (Fin 2) R} (hp : p.IsHomogeneous n) :
    (substitution R a p).IsHomogeneous n := by
  have hcol (j : Fin 2) : (∑ i, C (a i j) * X i).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (a i j) i
  simpa only [substitution, one_mul] using hp.aeval (fun j => ∑ i, C (a i j) * X i) hcol

/-- Matrix substitution restricted to homogeneous binary forms. -/
def action (n : ℕ) (a : Matrix (Fin 2) (Fin 2) R) :
    Module.End R (homogeneousSubmodule (Fin 2) R n) :=
  (substitution R a).toLinearMap.restrict fun _ hp => substitution_homogeneous R n a hp

/-- The coordinate matrix of substitution on degree-`n` binary forms. -/
def matrix (n : ℕ) (a : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  LinearMap.toMatrix (basis R n) (basis R n) (action R n a)

/-- The binary-form matrices preserve products. -/
theorem matrix_mul (n : ℕ) (a b : Matrix (Fin 2) (Fin 2) R) :
    matrix R n (a * b) = matrix R n a * matrix R n b := by
  have h : action R n (a * b) = (action R n a).comp (action R n b) := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact congrArg (fun f : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R => f p.val)
      (substitution_mul R a b)
  simp only [matrix, h, LinearMap.toMatrix_comp (basis R n) (basis R n) (basis R n)]

/-- The identity matrix acts identically on homogeneous binary forms. -/
theorem matrix_one (n : ℕ) : matrix R n 1 = 1 := by
  have h : action R n 1 = LinearMap.id := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact congrArg (fun f : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R => f p.val)
      (substitution_one R)
  rw [matrix, h, LinearMap.toMatrix_id]

/-- Monomial coefficients are the coordinates in the binary-form basis. -/
theorem basis_repr (n : ℕ) (p : homogeneousSubmodule (Fin 2) R n) (i : Fin (n + 1)) :
    (basis R n).repr p i = (p : MvPolynomial (Fin 2) R).coeff (exponent n i) := by
  let c := (lcoeff R (exponent n i)).comp (homogeneousSubmodule (Fin 2) R n).subtype
  change (basis R n).repr p i = c p
  have hc (j : Fin (n + 1)) : c (basis R n j) = if j = i then 1 else 0 := by
    simp only [c, LinearMap.comp_apply, Submodule.subtype_apply, lcoeff_apply, basis_coe,
      coeff_monomial, (exponent_injective n).eq_iff]
  have h := congrArg c ((basis R n).sum_repr p)
  simpa only [map_sum, map_smul, hc, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

/-- A binary-form matrix entry is the coefficient of the substituted monomial. -/
theorem matrix_apply (n : ℕ) (a : Matrix (Fin 2) (Fin 2) R) (i j : Fin (n + 1)) :
    matrix R n a i j =
      (substitution R a (monomial (exponent n j) 1)).coeff (exponent n i) := by
  rw [matrix, LinearMap.toMatrix_apply, basis_repr]
  change (substitution R a (basis R n j : MvPolynomial (Fin 2) R)).coeff _ = _
  rw [basis_coe]

variable {S : Type v} [CommRing S]

private theorem substitution_map (f : R →+* S) (a : Matrix (Fin 2) (Fin 2) R)
    (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (substitution R a p) =
      substitution S (a.map f) (MvPolynomial.map f p) := by
  have h : (MvPolynomial.map f).comp (substitution R a).toRingHom =
      (substitution S (a.map f)).toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change MvPolynomial.map f (substitution R a (C r)) =
        substitution S (a.map f) (MvPolynomial.map f (C r))
      rw [substitution_C, map_C, substitution_C]
    · intro j
      change MvPolynomial.map f (substitution R a (X j)) =
        substitution S (a.map f) (MvPolynomial.map f (X j))
      simp only [substitution_X, map_X, map_sum, map_mul, map_C, Matrix.map_apply]
  exact congrArg (fun q : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) S => q p) h

/-- Binary-form representation matrices commute with coefficient homomorphisms. -/
theorem matrix_map (n : ℕ) (f : R →+* S) (a : Matrix (Fin 2) (Fin 2) R) :
    matrix S n (a.map f) = (matrix R n a).map f := by
  ext i j
  rw [matrix_apply, Matrix.map_apply, matrix_apply, ← coeff_map]
  rw [substitution_map]
  simp only [map_monomial, map_one]

end ReductiveGroups.BinaryForms
