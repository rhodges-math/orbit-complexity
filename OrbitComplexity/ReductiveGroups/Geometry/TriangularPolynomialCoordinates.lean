import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Triangular Polynomial Coordinates

Polynomial inversion for finite strictly degree-triangular coordinate changes. -/

noncomputable section
namespace ReductiveGroups

open MvPolynomial

variable {ι K : Type*} [Fintype ι] [CommRing K]

omit [Fintype ι] in
private theorem aeval_eq_of_vars_eq
    {A : Type*} [CommRing A] [Algebra K A]
    (p : MvPolynomial ι K) (f g : ι → A)
    (h : ∀ i ∈ p.vars, f i = g i) : aeval f p = aeval g p := by
  simp only [aeval_eq_eval₂Hom]
  exact eval₂Hom_congr' rfl (fun i hi _ => h i hi) rfl

/-- Finite simultaneous substitution approximations for the inverse of a
strictly triangular polynomial coordinate change. -/
private def triangularInverseStage (q : ι → MvPolynomial ι K) :
    ℕ → ι → MvPolynomial ι K
  | 0, i => X i
  | m + 1, i => X i - aeval (triangularInverseStage q m) (q i)

omit [Fintype ι] in
private theorem triangularInverseStage_stable
    (d : ι → ℕ) (q : ι → MvPolynomial ι K)
    (hq : ∀ i j, j ∈ (q i).vars → d j < d i) :
    ∀ m i, d i < m →
      triangularInverseStage q (m + 1) i = triangularInverseStage q m i := by
  intro m
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
      intro i hi
      simp only [triangularInverseStage]
      congr 1
      apply aeval_eq_of_vars_eq
      intro j hj
      exact ih j (lt_of_lt_of_le (hq i j hj) (Nat.lt_succ_iff.mp hi))

/-- The polynomial inverse coordinates obtained after all degrees stabilize. -/
def triangularInverseCoordinates (d : ι → ℕ)
    (q : ι → MvPolynomial ι K) : ι → MvPolynomial ι K :=
  triangularInverseStage q ((Finset.univ.sup d) + 1)

private theorem triangularInverseCoordinates_fixed
    (d : ι → ℕ) (q : ι → MvPolynomial ι K)
    (hq : ∀ i j, j ∈ (q i).vars → d j < d i) (i : ι) :
    triangularInverseCoordinates d q i =
      X i - aeval (triangularInverseCoordinates d q) (q i) := by
  let N := Finset.univ.sup d + 1
  have hi : d i < N := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
  have hs := triangularInverseStage_stable d q hq N i hi
  change triangularInverseStage q N i =
    X i - aeval (triangularInverseStage q N) (q i)
  simpa only [triangularInverseStage] using hs.symm

/-- The explicit inverse substitution undoes the forward triangular
coordinates on every generator. -/
theorem triangularInverse_left
    (d : ι → ℕ) (q : ι → MvPolynomial ι K)
    (hq : ∀ i j, j ∈ (q i).vars → d j < d i) (i : ι) :
    aeval (triangularInverseCoordinates d q) (X i + q i) = X i := by
  simp only [map_add, aeval_X]
  have h := triangularInverseCoordinates_fixed d q hq i
  rw [h]
  abel

/-- Forward substitution also undoes the explicit inverse on every
generator, by induction on the strict degree. -/
theorem triangularInverse_right
    (d : ι → ℕ) (q : ι → MvPolynomial ι K)
    (hq : ∀ i j, j ∈ (q i).vars → d j < d i) (i : ι) :
    aeval (fun j => X j + q j) (triangularInverseCoordinates d q i) = X i := by
  let F : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
    aeval (fun j => X j + q j)
  have aux : ∀ n (i : ι), d i = n →
      F (triangularInverseCoordinates d q i) = X i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro i hi
        have hfix := triangularInverseCoordinates_fixed d q hq i
        have hvars : aeval (fun j => F (triangularInverseCoordinates d q j)) (q i) =
            q i := by
          calc
            _ = aeval (fun j : ι => X j) (q i) := by
              apply aeval_eq_of_vars_eq
              intro j hj
              exact ih (d j) (hi ▸ hq i j hj) j rfl
            _ = q i := aeval_X_left_apply _
        have hcomp := MvPolynomial.comp_aeval_apply
          (triangularInverseCoordinates d q) F (q i)
        have hmap := congrArg F hfix
        simp only [map_sub, hcomp, hvars] at hmap
        dsimp [F] at hmap ⊢
        simpa only [aeval_X, add_sub_cancel_right] using hmap
  exact aux (d i) i rfl

/-- A finite strictly degree-triangular polynomial coordinate change is
an algebra automorphism, including the empty index type and degree zero. -/
def triangularPolynomialAlgEquiv
    (d : ι → ℕ) (q : ι → MvPolynomial ι K)
    (hq : ∀ i j, j ∈ (q i).vars → d j < d i) :
    MvPolynomial ι K ≃ₐ[K] MvPolynomial ι K :=
  AlgEquiv.ofAlgHom (aeval (fun i => X i + q i))
    (aeval (triangularInverseCoordinates d q))
    (MvPolynomial.algHom_ext fun i => by
      simpa only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply] using
        triangularInverse_right d q hq i)
    (MvPolynomial.algHom_ext fun i => by
      simpa only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply] using
        triangularInverse_left d q hq i)

end ReductiveGroups
