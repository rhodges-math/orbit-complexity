import OrbitComplexity.GroupActions.Rosenlicht.LeadingGenerators
import Mathlib.LinearAlgebra.Projection

/-!
# Standard monomials in polynomial quotients

Division by polynomials with unit leading coefficients gives representatives
supported on standard monomials. Divisibility of every ideal leading monomial
makes these representatives unique, hence gives a basis of the quotient.
-/

open MvPolynomial

namespace GroupActions

noncomputable section

universe u v

variable {σ : Type u} {R : Type v} [CommRing R]

/-- Monomials divisible by none of the specified leading monomials. -/
def standardMonomials (m : MonomialOrder σ) (s : Finset (MvPolynomial σ R)) :
    Set (σ →₀ ℕ) := {d | ∀ p ∈ s, ¬ m.degree p ≤ d}

/-- The submodule of polynomials supported on standard monomials. -/
def normalForms (m : MonomialOrder σ) (s : Finset (MvPolynomial σ R)) :
    Submodule R (MvPolynomial σ R) := restrictSupport R (standardMonomials m s)

/-- Standard polynomials complement an ideal whose leading monomials are generated
by the specified polynomials with unit leading coefficients. -/
theorem isCompl_normalForms (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))
    (s : Finset (MvPolynomial σ R)) (hs : ∀ q ∈ s, q ∈ I)
    (hu : ∀ q ∈ s, IsUnit (m.leadingCoeff q))
    (hd : ∀ p ∈ I, p ≠ 0 → ∃ q ∈ s, m.degree q ≤ m.degree p) :
    IsCompl (I.restrictScalars R) (normalForms m s) := by
  classical
  constructor
  · apply Submodule.disjoint_def.mpr
    intro p hp hn
    by_contra h
    obtain ⟨q, hq, hqp⟩ := hd p hp h
    exact hn (m.degree_mem_support h) q hq hqp
  · rw [codisjoint_iff, eq_top_iff]
    intro p _
    obtain ⟨g, r, hpr, _, hr⟩ := m.div_set (B := (s : Set (MvPolynomial σ R))) hu p
    have hg : Finsupp.linearCombination (MvPolynomial σ R)
        (fun q : (s : Set (MvPolynomial σ R)) ↦ q.val) g ∈ I := by
      apply Submodule.sum_mem
      intro q _
      exact Submodule.smul_mem _ _ (hs q.val q.property)
    exact Submodule.mem_sup.mpr ⟨_, hg, r, hr, hpr.symm⟩

end

end GroupActions
