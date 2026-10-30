import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial coefficients on a common principal open

Finitely many elements of a fraction field lie in one localization away from
a nonzero denominator. Applying this to the coefficients of finitely many
polynomials lifts all those polynomials over the same localized ring.
-/

open scoped Classical

namespace GroupActions

noncomputable section

universe u v w

variable (R : Type u) [CommRing R]
variable (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]

/-- The canonical embedding of a principal localization into the fraction field. -/
def fractionAwayMap (r : R) (hr : r ≠ 0) : Localization.Away r →+* F :=
  Localization.awayLift (algebraMap R F) r
    (isUnit_iff_ne_zero.mpr (by
      intro h
      apply hr
      apply IsFractionRing.injective R F
      simpa only [map_zero] using h))

/-- The principal-localization embedding extends the original fraction-field map. -/
@[simp]
theorem fractionAwayMap_algebraMap (r : R) (hr : r ≠ 0) (a : R) :
    fractionAwayMap R F r hr (algebraMap R (Localization.Away r) a) = algebraMap R F a :=
  by simp only [fractionAwayMap, Localization.awayLift, IsLocalization.Away.lift_eq]

/-- The map from a principal localization into a fraction field is injective. -/
theorem fractionAwayMap_injective (r : R) (hr : r ≠ 0) :
    Function.Injective (fractionAwayMap R F r hr) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers r)
    (fractionAwayMap R F r hr)).mpr
  intro a b
  constructor
  · intro he
    simpa only [fractionAwayMap_algebraMap] using congrArg (fractionAwayMap R F r hr) he
  · intro he
    congr 1
    apply IsFractionRing.injective R F
    simpa only [fractionAwayMap_algebraMap] using he

/-- Finitely many fraction-field elements are regular on one nonempty principal open. -/
theorem exists_away_values (t : Finset F) :
    ∃ r : R, ∃ hr : r ≠ 0, ∀ f ∈ t, f ∈ Set.range (fractionAwayMap R F r hr) := by
  have : IsDomain R := Function.Injective.isDomain (algebraMap R F) (IsFractionRing.injective R F)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) t
  have hbn : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.property
  refine ⟨b, hbn, ?_⟩
  intro f hf
  obtain ⟨a, ha⟩ := hb f hf
  let j := fractionAwayMap R F b hbn
  let y : Localization.Away (b : R) := algebraMap R (Localization.Away (b : R)) a *
    IsLocalization.Away.invSelf (b : R)
  refine ⟨y, ?_⟩
  have hbf : algebraMap R F (b : R) ≠ 0 := by
    intro h
    apply hbn
    apply IsFractionRing.injective R F
    simpa only [map_zero] using h
  apply mul_left_cancel₀ hbf
  have he : algebraMap R (Localization.Away (b : R)) (b : R) * y =
      algebraMap R (Localization.Away (b : R)) a := by
    dsimp only [y]
    rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]
  change algebraMap R F (b : R) * j y = algebraMap R F (b : R) * f
  rw [← fractionAwayMap_algebraMap R F b hbn (b : R), ← map_mul, he]
  simpa only [j, fractionAwayMap_algebraMap, Algebra.smul_def] using ha

/-- Finitely many fraction-field polynomials lift to one principal localization. -/
theorem exists_away_polynomial_lifts {σ : Type w} (t : Finset (MvPolynomial σ F)) :
    ∃ r : R, ∃ hr : r ≠ 0, ∃ s : Finset (MvPolynomial σ (Localization.Away r)),
      s.image (MvPolynomial.map (fractionAwayMap R F r hr)) = t := by
  classical
  let c : Finset F := t.biUnion MvPolynomial.coeffs
  obtain ⟨r, hr, hc⟩ := exists_away_values R F c
  have hpoly (p : t) : ∃ q : MvPolynomial σ (Localization.Away r),
      MvPolynomial.map (fractionAwayMap R F r hr) q = p.val := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro a ha
    exact hc a (Finset.mem_biUnion.mpr ⟨p.val, p.property, ha⟩)
  choose b hb using hpoly
  refine ⟨r, hr, Finset.univ.image b, ?_⟩
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hq
    rw [hb z]
    exact z.property
  · intro hp
    refine Finset.mem_image.mpr ⟨b ⟨p, hp⟩,
      Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    exact hb ⟨p, hp⟩

end

end GroupActions
