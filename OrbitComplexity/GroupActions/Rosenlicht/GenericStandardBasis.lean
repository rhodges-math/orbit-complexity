import OrbitComplexity.GroupActions.Rosenlicht.LeadingLocalization

/-!
# Standard generators after localization

A polynomial ideal over a fraction field has a finite leading-monomial basis.
It lifts over one principal localization with unit leading coefficients, where
injectivity of the coefficient map descends leading-monomial divisibility.
-/

open MvPolynomial

namespace GroupActions

noncomputable section

universe u v w

variable (R : Type u) [CommRing R]
variable (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]

/-- A polynomial ideal over a fraction field has generators with unit leading
coefficients and the same leading-monomial divisibility over a principal localization. -/
theorem exists_away_leading_generators {σ : Type w} [Finite σ]
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ F)) :
    ∃ r : R, ∃ hr : r ≠ 0, ∃ s : Finset (MvPolynomial σ (Localization.Away r)),
      Ideal.map (MvPolynomial.map (fractionAwayMap R F r hr))
          (Ideal.span (s : Set (MvPolynomial σ (Localization.Away r)))) = I ∧
        (∀ q ∈ s, IsUnit (m.leadingCoeff q)) ∧
        ∀ p ∈ Ideal.span (s : Set (MvPolynomial σ (Localization.Away r))), p ≠ 0 →
          ∃ q ∈ s, m.degree q ≤ m.degree p := by
  classical
  obtain ⟨B, hB, hB0, hdeg⟩ := exists_polynomial_generators m I
  obtain ⟨r, hr, s, hs, hu⟩ := exists_away_unit_leading_lifts R F m B hB0
  let j := fractionAwayMap R F r hr
  have hj : Function.Injective j := fractionAwayMap_injective R F r hr
  have hI : Ideal.map (MvPolynomial.map j)
      (Ideal.span (s : Set (MvPolynomial σ (Localization.Away r)))) = I := by
    rw [Ideal.map_span, ← Finset.coe_image, hs, hB]
  refine ⟨r, hr, s, hI, hu, leading_generators_of_map m j hj s ?_⟩
  intro p hp hp0
  rw [hI] at hp
  obtain ⟨b, hb, hbp⟩ := hdeg p hp hp0
  have hb' : b ∈ s.image (MvPolynomial.map j) := by rw [hs]; exact hb
  obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hb'
  refine ⟨q, hq, ?_⟩
  rw [he]
  exact hbp

end

end GroupActions
