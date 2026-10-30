import OrbitComplexity.GroupActions.Rosenlicht.PolynomialLocalization
import OrbitComplexity.GroupActions.Rosenlicht.LeadingBaseChange

/-!
# Leading coefficients on a common principal open

Lifting the coefficients of finitely many polynomials and the inverses of their
leading coefficients gives polynomial lifts with unit leading coefficients.
The same principal localization works for the whole finite family.
-/

open MvPolynomial
open scoped Classical

namespace GroupActions

noncomputable section

universe u v w

variable (R : Type u) [CommRing R]
variable (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]

/-- A finite nonzero polynomial family over a fraction field lifts to a common
principal localization with invertible leading coefficients. -/
theorem exists_away_unit_leading_lifts {σ : Type w} (m : MonomialOrder σ)
    (t : Finset (MvPolynomial σ F)) (ht : ∀ p ∈ t, p ≠ 0) :
    ∃ r : R, ∃ hr : r ≠ 0, ∃ s : Finset (MvPolynomial σ (Localization.Away r)),
      s.image (MvPolynomial.map (fractionAwayMap R F r hr)) = t ∧
        ∀ q ∈ s, IsUnit (m.leadingCoeff q) := by
  classical
  let T := t ∪ t.image (fun p ↦ MvPolynomial.C (m.leadingCoeff p)⁻¹)
  obtain ⟨r, hr, S, hS⟩ := exists_away_polynomial_lifts R F T
  let j := fractionAwayMap R F r hr
  have hj : Function.Injective j := fractionAwayMap_injective R F r hr
  have hlift (p : t) : ∃ q ∈ S, MvPolynomial.map j q = p.val := by
    apply Finset.mem_image.mp
    rw [hS]
    exact Finset.mem_union_left _ p.property
  choose b hb hmap using hlift
  let s : Finset (MvPolynomial σ (Localization.Away r)) := Finset.univ.image b
  have hs : s.image (MvPolynomial.map j) = t := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hq
      rw [hmap z]
      exact z.property
    · intro hp
      refine Finset.mem_image.mpr ⟨b ⟨p, hp⟩,
        Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_univ _, rfl⟩, hmap ⟨p, hp⟩⟩
  refine ⟨r, hr, s, hs, ?_⟩
  intro q hq
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
  have hcT : MvPolynomial.C (m.leadingCoeff p.val)⁻¹ ∈ T :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩)
  rw [← hS] at hcT
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hcT
  have hc0 : j (c.coeff 0) = (m.leadingCoeff p.val)⁻¹ := by
    have he := congrArg (fun z : MvPolynomial σ F ↦ z.coeff 0) hc
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C] at he
    simpa only [eq_self, ite_true] using he
  have hlc : j (m.leadingCoeff (b p)) = m.leadingCoeff p.val := by
    rw [← hmap p]
    simp only [MonomialOrder.leadingCoeff, degree_map_of_injective m j hj,
      MvPolynomial.coeff_map]
  apply isUnit_iff_exists_inv.mpr
  refine ⟨c.coeff 0, ?_⟩
  apply hj
  rw [map_mul, hlc, hc0, map_one]
  exact mul_inv_cancel₀ (m.leadingCoeff_ne_zero_iff.mpr (ht p.val p.property))

end

end GroupActions
