import OrbitComplexity.GroupActions.Rosenlicht.StandardMonomials

/-!
# Descent of standard monomials through a coefficient embedding

An injective coefficient map preserves monomial degrees. Leading-monomial
divisibility over the extended coefficient field therefore descends to the
original coefficient ring, where unit leading coefficients give a quotient basis.
-/

open MvPolynomial

namespace GroupActions

noncomputable section

universe u v w

variable {σ : Type u} {R : Type v} {F : Type w}
variable [CommRing R] [Field F]

/-- An injective coefficient map preserves the degree for every monomial order. -/
theorem degree_map_of_injective (m : MonomialOrder σ) (f : R →+* F)
    (hf : Function.Injective f) (p : MvPolynomial σ R) :
    m.degree (MvPolynomial.map f p) = m.degree p := by
  simp only [MonomialOrder.degree, MvPolynomial.support_map_of_injective _ hf]

/-- Leading-monomial divisibility in the scalar extension of a polynomial ideal
implies the same divisibility over the original coefficient ring. -/
theorem leading_generators_of_map (m : MonomialOrder σ) (f : R →+* F)
    (hf : Function.Injective f) (s : Finset (MvPolynomial σ R))
    (hd : ∀ p ∈ Ideal.map (MvPolynomial.map f) (Ideal.span (s : Set (MvPolynomial σ R))),
      p ≠ 0 → ∃ q ∈ s, m.degree (MvPolynomial.map f q) ≤ m.degree p) :
    ∀ p ∈ Ideal.span (s : Set (MvPolynomial σ R)), p ≠ 0 →
      ∃ q ∈ s, m.degree q ≤ m.degree p := by
  intro p hp hp0
  have hpmap : MvPolynomial.map f p ∈
      Ideal.map (MvPolynomial.map f) (Ideal.span (s : Set (MvPolynomial σ R))) :=
    Ideal.mem_map_of_mem _ hp
  have hpmap0 : MvPolynomial.map f p ≠ 0 := by
    intro he
    exact hp0 ((MvPolynomial.map_injective f hf) (he.trans (map_zero _).symm))
  obtain ⟨q, hq, hdeg⟩ := hd _ hpmap hpmap0
  rw [degree_map_of_injective m f hf, degree_map_of_injective m f hf] at hdeg
  exact ⟨q, hq, hdeg⟩

end

end GroupActions
