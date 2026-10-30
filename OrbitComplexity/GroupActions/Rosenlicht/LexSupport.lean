import OrbitComplexity.GroupActions.Rosenlicht.QuotientSupports
import Mathlib.Algebra.MvPolynomial.Supported

/-!
# Elimination support in lexicographic order

When a set of variables is an upper set, its supported monomials are downward
closed in lexicographic order. Their image in a quotient with a leading-monomial
basis is therefore complemented by the other standard monomials.
-/

open MvPolynomial
open scoped MonomialOrder

namespace GroupActions

universe u v

variable {σ : Type u}

/-- Monomials supported on an upper set of variables are downward closed in
lexicographic monomial order. -/
theorem lex_support_of_upperSet [LinearOrder σ] [WellFoundedGT σ]
    (t : Set σ) (ht : IsUpperSet t) (a b : σ →₀ ℕ)
    (hab : a ≼[MonomialOrder.lex] b) (hb : (↑b.support : Set σ) ⊆ t) :
    (↑a.support : Set σ) ⊆ t := by
  by_cases he : a = b
  · simpa only [he] using hb
  change toLex a ≤ toLex b at hab
  have hn : toLex a ≠ toLex b := fun h ↦ he (congrArg ofLex h)
  obtain ⟨i, hbefore, hstep⟩ := Finsupp.Lex.lt_iff.mp (lt_of_le_of_ne hab hn)
  have hi : i ∈ t := hb (Finsupp.mem_support_iff.mpr
    (Nat.ne_of_gt ((Nat.zero_le (a i)).trans_lt hstep)))
  intro j hj
  by_contra hjt
  have hji : j < i := lt_of_not_ge fun hij ↦ hjt (ht hij hi)
  have hbj : b j = 0 := by
    by_contra h
    exact hjt (hb (Finsupp.mem_support_iff.mpr h))
  exact (Finsupp.mem_support_iff.mp hj) ((hbefore j hji).trans hbj)

section Semiring

variable (R : Type v) [CommSemiring R]

/-- A variable-supported polynomial subalgebra has the corresponding monomial
support submodule. -/
theorem supported_toSubmodule_eq (t : Set σ) :
    (MvPolynomial.supported R t).toSubmodule =
      restrictSupport R {d : σ →₀ ℕ | (↑d.support : Set σ) ⊆ t} := by
  ext p
  change p ∈ MvPolynomial.supported R t ↔ p ∈ restrictSupport R _
  rw [MvPolynomial.mem_supported, MvPolynomial.mem_restrictSupport_iff]
  constructor
  · intro hp d hd i hi
    exact hp ((MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩)
  · intro hp i hi
    obtain ⟨d, hd, hi⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
    exact hp hd hi

end Semiring

section Ring

variable {R : Type v} [CommRing R] [LinearOrder σ] [WellFoundedGT σ]

/-- The image of a final set of variables has a complement in any polynomial
quotient equipped with a lexicographic leading-monomial basis. -/
theorem isCompl_quotient_variables (s : Finset (MvPolynomial σ R))
    (hu : ∀ q ∈ s, IsUnit (MonomialOrder.lex.leadingCoeff q))
    (hd : ∀ p ∈ Ideal.span (s : Set (MvPolynomial σ R)), p ≠ 0 →
      ∃ q ∈ s, MonomialOrder.lex.degree q ≤ MonomialOrder.lex.degree p)
    (t : Set σ) (ht : IsUpperSet t) :
    IsCompl (((MvPolynomial.supported R t).toSubmodule).map
        ((Ideal.span (s : Set (MvPolynomial σ R))).restrictScalars R).mkQ)
      (quotientSupport (Ideal.span (s : Set (MvPolynomial σ R)))
        (standardMonomials MonomialOrder.lex s \ {d | (↑d.support : Set σ) ⊆ t})) := by
  rw [supported_toSubmodule_eq R t]
  exact isCompl_quotientSupport MonomialOrder.lex s hu hd _
    (lex_support_of_upperSet t ht)

end Ring

end GroupActions
