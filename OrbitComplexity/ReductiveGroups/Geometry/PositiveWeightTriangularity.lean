import OrbitComplexity.ReductiveGroups.Geometry.TriangularPolynomialCoordinates
import Mathlib.Data.Finsupp.Weight
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Positive Weight Triangularity

Positive weighted homogeneity and identity linear terms force strict
height triangularity of polynomial coordinate changes. -/

noncomputable section
namespace ReductiveGroups

open MvPolynomial

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]

omit [Fintype ι] [DecidableEq ι] in
private theorem monomial_eq_single_of_weight_ge
    (d : ι → ℕ) (hd : ∀ j, 0 < d j)
    (m : ι →₀ ℕ) (i j : ι)
    (hweight : m.weight d = d i)
    (hj : j ∈ m.support) (hge : d i ≤ d j) :
    m = Finsupp.single j 1 := by
  have hj0 : m j ≠ 0 := Finsupp.mem_support_iff.mp hj
  have hw := Finsupp.weight_sub_single_add (w := d) hj0
  rw [hweight] at hw
  have hzero : (m - Finsupp.single j 1).weight d = 0 := by omega
  have hmzero : m - Finsupp.single j 1 = 0 := by
    ext k
    have hk := Finsupp.le_weight d (Nat.ne_of_gt (hd k))
      (m - Finsupp.single j 1)
    rw [hzero] at hk
    exact Nat.eq_zero_of_le_zero hk
  have hm := Finsupp.sub_add_single_one_cancel hj0
  rw [hmzero, zero_add] at hm
  exact hm.symm

omit [Fintype ι] [DecidableEq ι] in
/-- Under positive weights, a homogeneous monomial of weight `d i`
containing a variable of weight at least `d i` must be that variable alone. -/
theorem positiveWeight_monomial_high_variable
    (d : ι → ℕ) (hd : ∀ j, 0 < d j)
    (p : ι → MvPolynomial ι K)
    (hw : ∀ i m, m ∈ (p i).support → m.weight d = d i)
    (i j : ι) (m : ι →₀ ℕ)
    (hm : m ∈ (p i).support) (hj : j ∈ m.support)
    (hge : d i ≤ d j) :
    m = Finsupp.single j 1 :=
  monomial_eq_single_of_weight_ge d hd m i j (hw i m hm) hj hge

omit [Fintype ι] in
/-- Removing the identity linear term leaves only strictly lower-weight
variables. This is the combinatorial triangularity criterion. -/
theorem positiveWeight_vars_sub_X_strict
    (d : ι → ℕ) (hd : ∀ j, 0 < d j)
    (p : ι → MvPolynomial ι K)
    (hw : ∀ i m, m ∈ (p i).support → m.weight d = d i)
    (hlinear : ∀ i j,
      (p i).coeff (Finsupp.single j 1) = if i = j then 1 else 0)
    (i : ι) :
    ((p i - X i).vars : Set ι) ⊆ {j | d j < d i} := by
  classical
  intro j hj
  by_contra hlt
  have hge : d i ≤ d j := Nat.le_of_not_gt hlt
  obtain ⟨m, hm, hjm⟩ := (mem_vars_iff_mem_support j).mp hj
  have hzero (k : ι) : (p i - X i).coeff (Finsupp.single k 1) = 0 := by
    rw [coeff_sub, hlinear]
    by_cases hik : i = k
    · subst k
      simp
    · simp [hik, coeff_X, Finsupp.single_eq_single_iff]
  have hmcase := (MvPolynomial.support_sub ι (p i) (X i)) hm
  rcases Finset.mem_union.mp hmcase with hp | hX
  · have heq := positiveWeight_monomial_high_variable d hd p hw i j m hp hjm hge
    rw [heq] at hm
    exact (MvPolynomial.mem_support_iff.mp hm) (hzero j)
  · have heq : m = Finsupp.single i 1 := by
      change m ∈ (monomial (Finsupp.single i 1) (1 : K)).support at hX
      exact Finset.mem_singleton.mp (support_monomial_subset hX)
    rw [heq] at hjm hm
    have hji : j = i := by
      simpa using hjm
    subst j
    exact (MvPolynomial.mem_support_iff.mp hm) (hzero i)

/-- Weighted homogeneity with positive degrees and identity linear part
makes the substitution a polynomial algebra automorphism. -/
def positiveWeightPolynomialAlgEquiv
    (d : ι → ℕ) (hd : ∀ j, 0 < d j)
    (p : ι → MvPolynomial ι K)
    (hw : ∀ i m, m ∈ (p i).support → m.weight d = d i)
    (hlinear : ∀ i j,
      (p i).coeff (Finsupp.single j 1) = if i = j then 1 else 0) :
    MvPolynomial ι K ≃ₐ[K] MvPolynomial ι K :=
  triangularPolynomialAlgEquiv d (fun i => p i - X i)
    (fun i _j hj => positiveWeight_vars_sub_X_strict d hd p hw hlinear i hj)

/-- The equality is

```lean
positiveWeightPolynomialAlgEquiv d hd p hw hlinear (X i) = p i
```
-/
@[simp] theorem positiveWeightPolynomialAlgEquiv_X
    (d : ι → ℕ) (hd : ∀ j, 0 < d j)
    (p : ι → MvPolynomial ι K)
    (hw : ∀ i m, m ∈ (p i).support → m.weight d = d i)
    (hlinear : ∀ i j,
      (p i).coeff (Finsupp.single j 1) = if i = j then 1 else 0)
    (i : ι) :
    positiveWeightPolynomialAlgEquiv d hd p hw hlinear (X i) = p i := by
  simp only [positiveWeightPolynomialAlgEquiv, triangularPolynomialAlgEquiv,
    AlgEquiv.ofAlgHom_apply, aeval_X]
  abel

end ReductiveGroups
