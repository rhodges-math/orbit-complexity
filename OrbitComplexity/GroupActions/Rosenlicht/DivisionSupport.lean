import OrbitComplexity.GroupActions.Rosenlicht.StandardMonomials

/-!
# Support of division remainders

Division does not increase monomial degree. Consequently a subspace spanned
by a downward closed collection of monomials has standard representatives
supported on the same collection.
-/

open MvPolynomial
open scoped MonomialOrder

namespace GroupActions

noncomputable section

universe u v

variable {σ : Type u} {R : Type v} [CommRing R]

/-- Division by polynomials with unit leading coefficients gives a remainder
whose monomial degree does not exceed that of the dividend. -/
theorem div_set_degree_le (m : MonomialOrder σ) (s : Finset (MvPolynomial σ R))
    (hu : ∀ q ∈ s, IsUnit (m.leadingCoeff q)) (p : MvPolynomial σ R) :
    ∃ (g : (s : Set (MvPolynomial σ R)) →₀ MvPolynomial σ R) (r : MvPolynomial σ R),
      p = Finsupp.linearCombination _ (fun q ↦ q.val) g + r ∧
        m.degree r ≼[m] m.degree p ∧ r ∈ normalForms m s := by
  classical
  obtain ⟨g, r, he, hg, hr⟩ := m.div_set (B := (s : Set (MvPolynomial σ R))) hu p
  have hsum : m.degree (Finsupp.linearCombination _
      (fun q : (s : Set (MvPolynomial σ R)) ↦ q.val) g) ≼[m] m.degree p := by
    change m.toSyn (m.degree (∑ q ∈ g.support, g q * q.val)) ≤ _
    exact m.degree_sum_le.trans (Finset.sup_le fun q _ ↦ by
      simpa only [mul_comm] using hg q)
  refine ⟨g, r, he, ?_, hr⟩
  have he' : r = p - Finsupp.linearCombination _
      (fun q : (s : Set (MvPolynomial σ R)) ↦ q.val) g := by
    rw [he, add_sub_cancel_left]
  rw [he']
  exact m.degree_sub_le.trans (sup_le le_rfl hsum)

/-- A polynomial supported on a downward closed set of monomials has a standard
representative with the same support constraint, modulo the generated ideal. -/
theorem exists_supported_normalForm (m : MonomialOrder σ)
    (s : Finset (MvPolynomial σ R)) (hu : ∀ q ∈ s, IsUnit (m.leadingCoeff q))
    (t : Set (σ →₀ ℕ))
    (ht : ∀ a b, a ≼[m] b → b ∈ t → a ∈ t)
    (p : MvPolynomial σ R) (hp : p ∈ restrictSupport R t) :
    ∃ r : MvPolynomial σ R, r ∈ normalForms m s ∧ r ∈ restrictSupport R t ∧
      p - r ∈ Ideal.span (s : Set (MvPolynomial σ R)) := by
  classical
  by_cases hp0 : p = 0
  · exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, by simp [hp0]⟩
  obtain ⟨g, r, he, hd, hr⟩ := div_set_degree_le m s hu p
  refine ⟨r, hr, ?_, ?_⟩
  · intro d hd'
    exact ht d (m.degree p) ((m.le_degree hd').trans hd) (hp (m.degree_mem_support hp0))
  · rw [he, add_sub_cancel_right]
    apply Submodule.sum_mem
    intro q _
    exact Submodule.smul_mem _ _ (Ideal.subset_span q.property)

end

end GroupActions
