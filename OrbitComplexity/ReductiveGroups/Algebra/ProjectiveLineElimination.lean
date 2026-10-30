import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import OrbitComplexity.ReductiveGroups.Algebra.PointZariski

/-!
# Projective Line Elimination

Completeness of the projective line, in the form needed for closedness
arguments on `K`-points: over an algebraically closed field `K` and a
finitely generated `K`-algebra `A`, the set of `K`-points `φ` of `A` over
which a family of binary forms with coefficients in `A` acquires a common
zero in `ℙ¹(K)` is closed for `pointZariskiTopology`.

The proof is classical elimination theory. Forms are dehomogenized at the
second coordinate, a finite subfamily is extracted by noetherianity, degrees
are equalized, and a common zero of forms `g₁, …, g_r` of formal degree `D`
is detected by the vanishing of all formal-degree `(D, D)` resultants of
`gᵢ` against the generic combinations `∑ vⱼ gⱼ`. These resultants are
polynomials in `v` with coefficients in `A`, and their coefficients cut out
the set. The Nullstellensatz is not used. -/

open Polynomial Topology

namespace ReductiveGroups

/-- A polynomial of `natDegree ≤ D`, with `D ≠ 0`, whose coefficient of `X ^ D`
vanishes has `natDegree < D`. -/
theorem NatDegree.lt_of_coeff_formalDegree_eq_zero {R : Type*} [Semiring R] {p : R[X]} {D : ℕ}
    (hD : D ≠ 0) (hp : p.natDegree ≤ D) (h : p.coeff D = 0) : p.natDegree < D := by
  refine lt_of_le_of_ne hp fun he => ?_
  have h0 : p.leadingCoeff = 0 := by rw [Polynomial.leadingCoeff, he, h]
  rw [leadingCoeff_eq_zero] at h0
  subst h0
  exact hD (by simpa using he.symm)

/-- Two polynomials of `natDegree ≤ D`, with `D ≠ 0`, having a common root have
vanishing formal-degree `(D, D)` resultant. -/
theorem ProjectiveLineElimination.formalDegree_eq_zero_of_eval_eq_zero {R : Type*} [CommRing R] {p q
  : R[X]}
    {D : ℕ} (hD : D ≠ 0) (hp : p.natDegree ≤ D) (hq : q.natDegree ≤ D) (t : R)
    (hpt : p.eval t = 0) (hqt : q.eval t = 0) : resultant p q D D = 0 := by
  obtain ⟨a, b, -, -, e⟩ := exists_mul_add_mul_eq_C_resultant p q hp hq (Or.inl hD)
  have := congrArg (eval t) e
  simpa [hpt, hqt] using this.symm

/-- Resultant criterion for a common zero in `ℙ¹(K)`, `K` algebraically closed.
Polynomials `gᵢ` of `natDegree ≤ D`, with `D ≠ 0`, are the dehomogenizations of
binary forms of degree `D`; they have a common zero in `ℙ¹(K)` (a common root,
or common vanishing of the `X ^ D` coefficients, i.e. a common zero at
infinity) if and only if every formal-degree `(D, D)` resultant of some `g i₀`
against a linear combination `∑ j, C (v j) * g j` vanishes. -/
theorem projectiveLine_commonZero_iff_resultant {K ι : Type*} [Field K] [IsAlgClosed K]
    [Fintype ι] (g : ι → K[X]) {D : ℕ} (hD : D ≠ 0) (hg : ∀ i, (g i).natDegree ≤ D) :
    ((∃ t, ∀ i, (g i).eval t = 0) ∨ ∀ i, (g i).coeff D = 0) ↔
      ∀ i₀ (v : ι → K), resultant (g i₀) (∑ j, C (v j) * g j) D D = 0 := by
  classical
  have hq : ∀ v : ι → K, (∑ j, C (v j) * g j).natDegree ≤ D := fun v =>
    natDegree_sum_le_of_forall_le _ _ fun j _ => (natDegree_C_mul_le _ _).trans (hg j)
  constructor
  · rintro (⟨t, ht⟩ | h) i₀ v
    · exact ProjectiveLineElimination.formalDegree_eq_zero_of_eval_eq_zero hD (hg i₀) (hq v) t (ht
      i₀)
        (by simp [eval_finsetSum, ht])
    · apply resultant_eq_zero_of_lt_lt
      · exact NatDegree.lt_of_coeff_formalDegree_eq_zero hD (hg i₀) (h i₀)
      · exact NatDegree.lt_of_coeff_formalDegree_eq_zero hD (hq v)
          (by simp [finsetSum_coeff, coeff_C_mul, h])
  · intro H
    by_contra hne
    push Not at hne
    obtain ⟨hroot, i₀, hi₀⟩ := hne
    set p := g i₀
    have hp0 : p ≠ 0 := fun h => hi₀ (by rw [h, coeff_zero])
    have hpD : p.natDegree = D := natDegree_eq_of_le_of_coeff_ne_zero (hg i₀) hi₀
    obtain ⟨v, hv⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
      (ι := {a // a ∈ p.roots.toFinset}) (M := ι → K)
      (fun a => Fintype.linearCombination K (fun i => (g i).eval a.1)) (fun a => by
        obtain ⟨i, hi⟩ := hroot a.1
        refine ⟨Pi.single i 1, ?_⟩
        simpa [Fintype.linearCombination_apply, Pi.single_apply] using hi)
    set q := ∑ j, C (v j) * g j
    have hcop : IsCoprime p q := by
      rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) K]
      intro a
      by_cases ha : p.eval a = 0
      · right
        have hmem : a ∈ p.roots.toFinset := by
          rw [Multiset.mem_toFinset, mem_roots hp0]
          exact ha
        have := hv ⟨a, hmem⟩
        simpa [q, Fintype.linearCombination_apply, eval_finsetSum] using this
      · left
        simpa using ha
    apply resultant_ne_zero p q hcop
    have hqD := hq v
    have key := resultant_add_right_deg p q D q.natDegree (D - q.natDegree) le_rfl
    rw [Nat.add_sub_cancel' hqD] at key
    have hres := H i₀ v
    rw [key] at hres
    rcases mul_eq_zero.mp hres with h1 | h1
    · exact absurd (pow_eq_zero_iff'.mp h1).1 hi₀
    · show resultant p q p.natDegree q.natDegree = 0
      rw [hpD]
      exact h1

section Dehomogenize

variable {R : Type*} [CommRing R]

/-- The dehomogenization `F(X, 1)` of a polynomial `F` in two variables. -/
noncomputable def binaryFormDehomogenize (F : MvPolynomial (Fin 2) R) : R[X] :=
  MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, 1] F

/-- The dehomogenization `F(X, 1)` as a sum over the support of `F`. -/
theorem binaryFormDehomogenize_eq_sum (F : MvPolynomial (Fin 2) R) :
    binaryFormDehomogenize F = ∑ d ∈ F.support, C (F.coeff d) * X ^ (d 0) := by
  rw [binaryFormDehomogenize, MvPolynomial.eval₂_eq']
  simp [Fin.prod_univ_two]

/-- Every exponent `d` in the support of a homogeneous `F` of degree `n` in two
variables satisfies `d 0 + d 1 = n`. -/
theorem binaryForm_support_add {F : MvPolynomial (Fin 2) R} {n : ℕ} (hF : F.IsHomogeneous n)
    {d : Fin 2 →₀ ℕ} (hd : d ∈ F.support) : d 0 + d 1 = n := by
  have h := hF.degree_eq_sum_deg_support hd
  rw [← Finsupp.degree_apply, Finsupp.degree_eq_sum, Fin.sum_univ_two] at h
  exact h.symm

/-- The dehomogenization of a binary form of degree `n` has `natDegree ≤ n`. -/
theorem binaryFormDehomogenize_natDegree_le {F : MvPolynomial (Fin 2) R} {n : ℕ}
    (hF : F.IsHomogeneous n) : (binaryFormDehomogenize F).natDegree ≤ n := by
  rw [binaryFormDehomogenize_eq_sum]
  refine natDegree_sum_le_of_forall_le _ _ fun d hd => (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := binaryForm_support_add hF hd
  omega

/-- Evaluating the `φ`-specialized dehomogenization at `t` is evaluating the
`φ`-specialized form at `(t, 1)`. -/
theorem binaryFormDehomogenize_eval_map {S : Type*} [CommRing S] (φ : R →+* S)
    (F : MvPolynomial (Fin 2) R) (t : S) :
    ((binaryFormDehomogenize F).map φ).eval t = MvPolynomial.eval₂ φ ![t, 1] F := by
  rw [binaryFormDehomogenize_eq_sum, MvPolynomial.eval₂_eq', Polynomial.map_sum, eval_finsetSum]
  simp [Fin.prod_univ_two]

/-- For a binary form `F` of degree `n`, `φ` of the `X ^ n` coefficient of its
dehomogenization is the value of the `φ`-specialized form at `(1, 0)`. -/
theorem binaryFormDehomogenize_coeff_map {S : Type*} [CommRing S] (φ : R →+* S)
    {F : MvPolynomial (Fin 2) R} {n : ℕ} (hF : F.IsHomogeneous n) :
    φ ((binaryFormDehomogenize F).coeff n) = MvPolynomial.eval₂ φ ![1, 0] F := by
  rw [binaryFormDehomogenize_eq_sum, MvPolynomial.eval₂_eq', finsetSum_coeff, map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h := binaryForm_support_add hF hd
  simp only [coeff_C_mul, coeff_X_pow, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_pow, one_mul]
  by_cases h1 : d 1 = 0
  · rw [ite_eq_left (by omega), h1, pow_zero, mul_one, mul_one]
  · rw [ite_eq_right (by omega), zero_pow h1, mul_zero, mul_zero, map_zero]

/-- Homogeneity of evaluation: a binary form of degree `n` satisfies
`F(a • x) = a ^ n * F(x)` after specialization along `φ`. -/
theorem binaryForm_eval₂_smul {S : Type*} [CommRing S] (φ : R →+* S)
    {F : MvPolynomial (Fin 2) R} {n : ℕ} (hF : F.IsHomogeneous n) (a : S) (x : Fin 2 → S) :
    MvPolynomial.eval₂ φ (a • x) F = a ^ n * MvPolynomial.eval₂ φ x F := by
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← binaryForm_support_add hF hd]
  simp only [Fin.prod_univ_two, Pi.smul_apply, smul_eq_mul, mul_pow, pow_add]
  ring

/-- A family of binary forms, specialized along `φ : R →+* K` into a field, has a
common nonzero zero `c : Fin 2 → K` if and only if it has a common zero of the
form `(t, 1)` or a common zero at `(1, 0)`. -/
theorem binaryForms_commonZero_iff {K ι : Type*} [Field K] (φ : R →+* K)
    (G : ι → MvPolynomial (Fin 2) R) (n : ι → ℕ) (hG : ∀ i, (G i).IsHomogeneous (n i)) :
    (∃ c : Fin 2 → K, c ≠ 0 ∧ ∀ i, MvPolynomial.eval₂ φ c (G i) = 0) ↔
      (∃ t : K, ∀ i, MvPolynomial.eval₂ φ ![t, 1] (G i) = 0) ∨
        ∀ i, MvPolynomial.eval₂ φ ![1, 0] (G i) = 0 := by
  constructor
  · rintro ⟨c, hc, hcG⟩
    by_cases h1 : c 1 = 0
    · have h0 : c 0 ≠ 0 := by
        intro h0
        apply hc
        funext j
        fin_cases j <;> simp [h0, h1]
      have hc' : c = c 0 • ![1, 0] := by
        funext j
        fin_cases j <;> simp [h1]
      right
      intro i
      have := hcG i
      rw [hc', binaryForm_eval₂_smul φ (hG i)] at this
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ h0)
    · have hc' : c = c 1 • ![c 0 / c 1, 1] := by
        funext j
        fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
          field_simp
        · simp
      left
      refine ⟨c 0 / c 1, fun i => ?_⟩
      have := hcG i
      rw [hc', binaryForm_eval₂_smul φ (hG i)] at this
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ h1)
  · rintro (⟨t, ht⟩ | h)
    · exact ⟨![t, 1], fun h => by simpa using congrFun h 1, ht⟩
    · exact ⟨![1, 0], fun h => by simpa using congrFun h 0, h⟩

end Dehomogenize

section Elimination

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The eliminant of a finite family `f` of polynomials over `A` in formal
degree `D`, indexed by `i₀`: the formal-degree `(D, D)` resultant of `f i₀`
against the generic combination `∑ j, X j * f j`, computed over
`MvPolynomial ι A`. -/
noncomputable def projectiveLineEliminant {ι : Type*} [Fintype ι] (f : ι → A[X]) (D : ℕ)
    (i₀ : ι) : MvPolynomial ι A :=
  resultant ((f i₀).map MvPolynomial.C)
    (∑ j, Polynomial.C (MvPolynomial.X j) * (f j).map MvPolynomial.C) D D

/-- Specializing the eliminant along `φ : A →+* S` and the variables at `v` gives
the formal-degree `(D, D)` resultant of the specialized `f i₀` against
`∑ j, C (v j) * (f j).map φ`. -/
theorem projectiveLineEliminant_eval_map {S : Type*} [CommRing S] {ι : Type*} [Fintype ι]
    (f : ι → A[X]) (D : ℕ) (i₀ : ι) (φ : A →+* S) (v : ι → S) :
    MvPolynomial.eval v (MvPolynomial.map φ (projectiveLineEliminant f D i₀)) =
      resultant ((f i₀).map φ) (∑ j, Polynomial.C (v j) * (f j).map φ) D D := by
  rw [MvPolynomial.eval_map, projectiveLineEliminant, ← MvPolynomial.coe_eval₂Hom,
    ← resultant_map_map]
  have hC : (MvPolynomial.eval₂Hom φ v).comp MvPolynomial.C = φ := by
    ext a
    simp
  congr 1
  · rw [Polynomial.map_map, hC]
  · simp [Polynomial.map_sum, Polynomial.map_map, hC]

/-- Affine-chart elimination in a single formal degree `D ≠ 0`: for a finite
family `f` of polynomials over `A` of `natDegree ≤ D`, the set of `K`-points
over which the specialized family has a common root in `K` or a common zero at
infinity (vanishing `X ^ D` coefficients) is closed for `pointZariskiTopology`. -/
theorem ProjectiveLineElimination.isClosed_affineChart_of_formalDegree [IsAlgClosed K] {ι : Type*}
    [Fintype ι] (f : ι → A[X]) {D : ℕ} (hD : D ≠ 0) (hf : ∀ i, (f i).natDegree ≤ D) :
    IsClosed[pointZariskiTopology] {φ : A →ₐ[K] K |
      (∃ t : K, ∀ i, ((f i).map (φ : A →+* K)).eval t = 0) ∨ ∀ i, φ ((f i).coeff D) = 0} := by
  rw [pointZariski_isClosed_iff]
  refine ⟨{a | ∃ i₀ m, (projectiveLineEliminant f D i₀).coeff m = a}, ?_⟩
  ext φ
  have hK := projectiveLine_commonZero_iff_resultant (fun i => (f i).map (φ : A →+* K)) hD
    (fun i => natDegree_map_le.trans (hf i))
  simp only [coeff_map, AlgHom.coe_toRingHom] at hK
  simp only [Set.mem_ofPred_eq, pointZeroLocus]
  rw [hK]
  constructor
  · rintro H a ⟨i₀, m, rfl⟩
    have h0 : MvPolynomial.map (φ : A →+* K) (projectiveLineEliminant f D i₀) = 0 := by
      apply MvPolynomial.funext
      intro v
      rw [projectiveLineEliminant_eval_map, map_zero]
      exact H i₀ v
    have := congrArg (·.coeff m) h0
    simpa [MvPolynomial.coeff_map] using this
  · intro H i₀ v
    have h0 : MvPolynomial.map (φ : A →+* K) (projectiveLineEliminant f D i₀) = 0 := by
      ext m
      simpa [MvPolynomial.coeff_map] using H _ ⟨i₀, m, rfl⟩
    rw [← projectiveLineEliminant_eval_map, h0, map_zero]

/-- Affine-chart form of the completeness of `ℙ¹`: for a finite family `f` of
polynomials over `A` with `natDegree (f i) ≤ d i`, the set of `K`-points `φ`
over which the specialized family has a common root in `K`, or all the
coefficients `φ ((f i).coeff (d i))` vanish (a common zero at infinity), is
closed for `pointZariskiTopology`. -/
theorem isClosed_projectiveLine_affineChart [IsAlgClosed K] {ι : Type*} [Finite ι]
    (f : ι → A[X]) (d : ι → ℕ) (hf : ∀ i, (f i).natDegree ≤ d i) :
    IsClosed[pointZariskiTopology] {φ : A →ₐ[K] K |
      (∃ t : K, ∀ i, ((f i).map (φ : A →+* K)).eval t = 0) ∨
        ∀ i, φ ((f i).coeff (d i)) = 0} := by
  cases nonempty_fintype ι
  set D := ∑ i, d i + 1
  have hdD : ∀ i, d i < D := fun i => Nat.lt_succ_of_le
    (Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i))
  let f' : ι ⊕ ι → A[X] := Sum.elim f (fun i => X ^ (D - d i) * f i)
  have hf' : ∀ j, (f' j).natDegree ≤ D := by
    rintro (i | i)
    · exact (hf i).trans (hdD i).le
    · calc (X ^ (D - d i) * f i).natDegree
          ≤ (X ^ (D - d i) : A[X]).natDegree + (f i).natDegree := natDegree_mul_le
        _ ≤ (D - d i) + d i := add_le_add (natDegree_X_pow_le _) (hf i)
        _ = D := Nat.sub_add_cancel (hdD i).le
  convert ProjectiveLineElimination.isClosed_affineChart_of_formalDegree (K := K) f'
    (by omega : D ≠ 0) hf' using 1
  ext φ
  simp only [Set.mem_ofPred_eq, Sum.forall, f', Sum.elim_inl, Sum.elim_inr]
  apply or_congr
  · apply exists_congr
    intro t
    constructor
    · intro h
      exact ⟨h, fun i => by simp [h i]⟩
    · exact And.left
  · have hX : ∀ i, (X ^ (D - d i) * f i).coeff D = (f i).coeff (d i) := fun i => by
      rw [coeff_X_pow_mul', ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self (hdD i).le]
    have hz : ∀ i, (f i).coeff D = 0 := fun i =>
      coeff_eq_zero_of_natDegree_lt ((hf i).trans_lt (hdD i))
    simp only [hX, hz, map_zero, implies_true, true_and]

/-- Completeness of the projective line: for `A` a finitely generated algebra
over an algebraically closed field `K` and any family `H` of homogeneous
polynomials in two variables over `A`, the set of `K`-points `φ` over which
the specialized family has a common zero `c ≠ 0` in `K²` is closed for
`pointZariskiTopology`. -/
theorem isClosed_projectiveLine_commonZero [IsAlgClosed K] [Algebra.FiniteType K A]
    (H : Set (MvPolynomial (Fin 2) A)) (hH : ∀ F ∈ H, ∃ n, F.IsHomogeneous n) :
    IsClosed[pointZariskiTopology] {φ : A →ₐ[K] K | ∃ c : Fin 2 → K, c ≠ 0 ∧
      ∀ F ∈ H, MvPolynomial.eval c (MvPolynomial.map (φ : A →+* K) F) = 0} := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  obtain ⟨H₀, hH₀H, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset H).mp
    (IsNoetherian.noetherian (Ideal.span H))
  have hred : ∀ ψ : MvPolynomial (Fin 2) A →+* K,
      (∀ F ∈ H, ψ F = 0) ↔ ∀ F : H₀, ψ F.1 = 0 := by
    intro ψ
    constructor
    · intro h F
      exact h F.1 (hH₀H F.2)
    · intro h F hF
      have hle : Ideal.span (H₀ : Set (MvPolynomial (Fin 2) A)) ≤ RingHom.ker ψ :=
        Ideal.span_le.mpr fun G hG => h ⟨G, hG⟩
      have hmem : F ∈ Submodule.span (MvPolynomial (Fin 2) A) (H₀ : Set _) :=
        hspan ▸ Submodule.subset_span hF
      exact hle hmem
  choose n hn using hH
  let G : H₀ → MvPolynomial (Fin 2) A := fun F => F.1
  let deg : H₀ → ℕ := fun F => n F.1 (hH₀H F.2)
  have hG : ∀ F : H₀, (G F).IsHomogeneous (deg F) := fun F => hn F.1 (hH₀H F.2)
  convert isClosed_projectiveLine_affineChart (K := K) (fun F => binaryFormDehomogenize (G F))
    deg (fun F => binaryFormDehomogenize_natDegree_le (hG F)) using 1
  ext φ
  simp only [Set.mem_ofPred_eq]
  have e1 : (∃ c : Fin 2 → K, c ≠ 0 ∧
      ∀ F ∈ H, MvPolynomial.eval c (MvPolynomial.map (φ : A →+* K) F) = 0) ↔
      ∃ c : Fin 2 → K, c ≠ 0 ∧ ∀ F : H₀, MvPolynomial.eval₂ (φ : A →+* K) c (G F) = 0 := by
    apply exists_congr
    intro c
    apply and_congr_right
    intro _
    simpa [MvPolynomial.eval_map] using hred (MvPolynomial.eval₂Hom (φ : A →+* K) c)
  have hcoeff : ∀ F : H₀, φ ((binaryFormDehomogenize (G F)).coeff (deg F)) =
      MvPolynomial.eval₂ (φ : A →+* K) ![1, 0] (G F) :=
    fun F => binaryFormDehomogenize_coeff_map (φ : A →+* K) (hG F)
  rw [e1, binaryForms_commonZero_iff (φ : A →+* K) G deg hG]
  simp only [binaryFormDehomogenize_eval_map, hcoeff]

end Elimination

end ReductiveGroups
