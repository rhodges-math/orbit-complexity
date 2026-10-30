import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

/-!
# Normal subgroups of `GL_n` consisting of unipotent matrices are trivial

Let `F` be a field and let `N` be a normal subgroup of `GL_n(F)` all of whose elements are
unipotent. Then `N` is trivial.

A unipotent matrix has trace `n`. Suppose `u = 1 + x ∈ N` with `x ≠ 0`. Since `x` is nilpotent
it is not diagonal, so `x_ab ≠ 0` for some `a ≠ b`. Put `E = c e_ba` with `c = x_ab⁻¹`, so
`E² = 0`, and `h = 1 + E`. Then `u · h u h⁻¹ ∈ N`, while a direct computation using
`tr x = tr x² = 0` gives `tr(u · h u h⁻¹) = n - (c x_ab)² = n - 1`, a contradiction.

This elementary argument replaces the usual appeal to Kolchin's fixed-point theorem
(a unipotent group fixes a nonzero vector; the fixed space of a normal subgroup is stable, hence
everything by irreducibility of the standard representation).

## Main declarations

* `ReductiveGroups.GLn.trace_eq_card_of_isNilpotent_sub_one`: unipotent matrices have trace `n`.
* `ReductiveGroups.GLn.eq_bot_of_normal_of_forall_isNilpotent`: a normal subgroup of unipotent
  matrices is trivial.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §§4.8 and 11.21.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §§17.5 and 19.5.
* T. A. Springer, *Linear Algebraic Groups*, 2nd ed. (1998), §§2.4 and 7.6.
-/

namespace ReductiveGroups.GLn

open Matrix

variable {F : Type*} [Field F] {n : ℕ}

/-- A unipotent matrix has trace `n`. -/
theorem trace_eq_card_of_isNilpotent_sub_one {g : Matrix (Fin n) (Fin n) F}
    (hg : IsNilpotent (g - 1)) : g.trace = n := by
  have h := (Matrix.isNilpotent_trace_of_isNilpotent hg).eq_zero
  rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, sub_eq_zero] at h
  exact h

/-- A nonzero nilpotent matrix over a field has a nonzero off-diagonal entry. -/
theorem exists_offDiagonal_ne_zero {x : Matrix (Fin n) (Fin n) F} (hx : IsNilpotent x)
    (hx0 : x ≠ 0) : ∃ a b, a ≠ b ∧ x a b ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hdiag : x = Matrix.diagonal fun i => x i i := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hab]
      exact hcon a b hab
  apply hx0
  obtain ⟨k, hk⟩ := hx
  rw [hdiag, Matrix.diagonal_pow] at hk
  rw [hdiag]
  ext a b
  have hnil : IsNilpotent (x a a) := ⟨k, by simpa using congrFun (congrFun hk a) a⟩
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq, hnil.eq_zero]
    rfl
  · rw [Matrix.diagonal_apply_ne _ hab]
    rfl

/-- The trace identity behind the triviality of normal unipotent subgroups. -/
theorem trace_conj_product (x E : Matrix (Fin n) (Fin n) F) (hE : E * E = 0)
    (hx : x.trace = 0) (hx2 : (x * x).trace = 0) :
    ((1 + x) * ((1 + E) * (1 + x) * (1 - E))).trace = n - (x * E * x * E).trace := by
  have hexp : (1 + x) * ((1 + E) * (1 + x) * (1 - E)) =
      1 + x + x + x * x + (E * x - x * E) + (x * E * x - x * x * E) - E * x * E -
        x * E * x * E - (E * E + x * (E * E)) := by
    noncomm_ring
  rw [hexp, hE, Matrix.mul_zero, add_zero]
  have h1 : (E * x - x * E).trace = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  have h2 : (x * E * x - x * x * E).trace = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_cycle, Matrix.mul_assoc, sub_self]
  have h3 : (E * x * E).trace = 0 := by
    rw [Matrix.trace_mul_cycle, hE, Matrix.zero_mul, Matrix.trace_zero]
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin, hx, hx2,
    h1, h2, h3, Matrix.trace_zero]
  ring

/-- **A normal subgroup of `GL_n(F)` consisting of unipotent matrices is trivial.** -/
theorem eq_bot_of_normal_of_forall_isNilpotent (N : Subgroup (GL (Fin n) F)) [hN : N.Normal]
    (hnil : ∀ g ∈ N, IsNilpotent ((g : Matrix (Fin n) (Fin n) F) - 1)) : N = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  by_contra hne
  set x : Matrix (Fin n) (Fin n) F := (u : Matrix (Fin n) (Fin n) F) - 1 with hxdef
  have hu' : (u : Matrix (Fin n) (Fin n) F) = 1 + x := by
    rw [hxdef, add_sub_cancel]
  have hx0 : x ≠ 0 := by
    intro h
    apply hne
    apply Units.ext
    rw [hu', h, add_zero, Units.val_one]
  obtain ⟨a, b, hab, hxab⟩ := exists_offDiagonal_ne_zero (hnil u hu) hx0
  have htx : x.trace = 0 := by
    have h := trace_eq_card_of_isNilpotent_sub_one (hnil u hu)
    rw [hu', Matrix.trace_add, Matrix.trace_one, Fintype.card_fin] at h
    linear_combination h
  have htx2 : (x * x).trace = 0 := by
    have h := trace_eq_card_of_isNilpotent_sub_one (hnil (u * u) (N.mul_mem hu hu))
    have hexp : (1 + x) * (1 + x) = 1 + x + x + x * x := by noncomm_ring
    rw [Units.val_mul, hu', hexp, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
      Matrix.trace_one, Fintype.card_fin, htx] at h
    linear_combination h
  set c : F := (x a b)⁻¹ with hc
  set E : Matrix (Fin n) (Fin n) F := Matrix.single b a c with hEdef
  have hE : E * E = 0 := by simp [hEdef, hab]
  have hEinv : (1 + E) * (1 - E) = 1 := by
    rw [show (1 + E) * (1 - E) = 1 - E * E by noncomm_ring, hE, sub_zero]
  have hEinv' : (1 - E) * (1 + E) = 1 := by
    rw [show (1 - E) * (1 + E) = 1 - E * E by noncomm_ring, hE, sub_zero]
  let h : GL (Fin n) F := ⟨1 + E, 1 - E, hEinv, hEinv'⟩
  have hconj : h * u * h⁻¹ ∈ N := hN.conj_mem u hu h
  have htr := trace_eq_card_of_isNilpotent_sub_one (hnil _ (N.mul_mem hu hconj))
  have hcoe : ((u * (h * u * h⁻¹) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (1 + x) * ((1 + E) * (1 + x) * (1 - E)) := by
    simp only [Units.val_mul, hu']
    rfl
  have hxExE : (x * E * x * E).trace = 1 := by
    rw [Matrix.mul_assoc x E x, Matrix.mul_assoc, hEdef, Matrix.single_mul_mul_single,
      Matrix.trace_mul_single]
    have hxab' : x a b ≠ 0 := hxab
    rw [op_smul_eq_mul, hc]
    field_simp
  rw [hcoe, trace_conj_product x E hE htx htx2, hxExE] at htr
  have h10 : (1 : F) = 0 := by linear_combination -htr
  exact one_ne_zero h10

end GLn
