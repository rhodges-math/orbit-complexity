import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Ring.Subring.Basic

/-! # The absolute Frobenius image in a polynomial coordinate -/

namespace FrobeniusSplitting
open Polynomial
noncomputable section
universe u
variable (A : Type u) [CommRing A] (p : ℕ) [ExpChar A p]

/-- Polynomials over the coefficient Frobenius image embed with p-divisible exponents. -/
def polynomialPowerMap : Polynomial (frobenius A p).range →+* Polynomial A :=
  (Polynomial.expand A p).toRingHom.comp
    (Polynomial.mapRingHom (frobenius A p).range.subtype)

/-- The coefficient-image presentation embeds even when the coefficient ring is nonreduced. -/
theorem polynomialPowerMap_injective : Function.Injective (polynomialPowerMap A p) :=
  (Polynomial.expand_injective (expChar_pos A p)).comp
    (Polynomial.map_injective (frobenius A p).range.subtype
      (Subring.subtype_injective (frobenius A p).range))

private theorem powerMap_frobenius (f : Polynomial A) :
    polynomialPowerMap A p (Polynomial.map (frobenius A p).rangeRestrict f) = f ^ p := by
  change Polynomial.expand A p
    (Polynomial.map (frobenius A p).range.subtype
      (Polynomial.map (frobenius A p).rangeRestrict f)) = _
  rw [Polynomial.map_map]
  change Polynomial.expand A p (Polynomial.map (frobenius A p) f) = _
  rw [← Polynomial.map_expand, Polynomial.map_frobenius_expand]

/-- The image is the absolute pth-power subring, with coefficients in A^p rather than A. -/
theorem polynomialPowerMap_range :
    (polynomialPowerMap A p).range = (frobenius (Polynomial A) p).range := by
  ext f
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨r, hr⟩ := Polynomial.map_surjective (frobenius A p).rangeRestrict
      (RingHom.rangeRestrict_surjective (frobenius A p)) q
    refine ⟨r, ?_⟩
    change r ^ p = polynomialPowerMap A p q
    rw [← hr, powerMap_frobenius]
  · rintro ⟨q, rfl⟩
    exact ⟨Polynomial.map (frobenius A p).rangeRestrict q, powerMap_frobenius A p q⟩

end
end FrobeniusSplitting
