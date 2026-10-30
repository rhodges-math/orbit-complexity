import OrbitComplexity.FrobeniusSplitting.Cartier.OperatorCharts
import OrbitComplexity.FrobeniusSplitting.Cartier.Jacobian

/-! # Trace frames in reciprocal open charts -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace FrobeniusSplitting

private theorem localize_weight {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {p : ℕ} (M : Submonoid R) [IsLocalization M S]
    (φ : FrobeniusLinearMap R p) (hp : 0 < p) (r : R) :
    (φ.weight r).localize (S := S) M hp =
      (φ.localize (S := S) M hp).weight (algebraMap R S r) := by
  apply FrobeniusLinearMap.localize_eq
  intro a
  change φ.localize M hp (algebraMap R S r * algebraMap R S a) =
    algebraMap R S (φ (r * a))
  rw [← (algebraMap R S).map_mul, FrobeniusLinearMap.localize_algebraMap]

/-- Multiplication by a coordinate-ring weight agrees with input weighting on the spectrum. -/
theorem traceWeight_toSpec {R : Type u} [CommRing R] {p : ℕ}
    (φ : FrobeniusLinearMap R p) (hp : 0 < p) (r : R) :
    (φ.weight r).toSpec hp =
      (φ.toSpec hp).inputWeight ((Scheme.ΓSpecIso (.of R)).inv r) := by
  ext U m
  apply Subtype.ext
  funext x
  change ((φ.weight r).localize (S := Localization x.1.asIdeal.primeCompl)
      x.1.asIdeal.primeCompl hp) (m.1 x) =
    (φ.localize (S := Localization x.1.asIdeal.primeCompl) x.1.asIdeal.primeCompl hp)
      (algebraMap R (Localization x.1.asIdeal.primeCompl) r * m.1 x)
  exact congrArg (fun ψ : FrobeniusLinearMap (Localization x.1.asIdeal.primeCompl) p =>
    ψ (m.1 x)) (localize_weight x.1.asIdeal.primeCompl φ hp r)

variable (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]

private def inclusion : Spec (.of (LaurentPolynomial C)) ⟶ Spec (.of (Polynomial C)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial C →+* LaurentPolynomial C))

private instance inclusion_open : IsOpenImmersion (inclusion C) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial C)

private def inversion : Spec (.of (LaurentPolynomial C)) ⟶
    Spec (.of (LaurentPolynomial C)) :=
  Spec.map (CommRingCat.ofHom
    (LaurentPolynomial.invert : LaurentPolynomial C ≃ₐ[C] LaurentPolynomial C).toRingHom)

private instance inversion_iso : IsIso (inversion C) :=
  inferInstanceAs (IsIso (Scheme.Spec.mapIso
    (LaurentPolynomial.invert : LaurentPolynomial C ≃ₐ[C]
      LaurentPolynomial C).toRingEquiv.toCommRingCatIso.op).hom)

/-- The polynomial trace frame pulls back to the Laurent trace frame. -/
theorem traceFrame_toLaurent (base : RingSplitting C p) :
    ((univariateTrace base).toSpec (expChar_pos C p)).openPullback (inclusion C) =
      (laurentTrace base).toSpec (expChar_pos C p) :=
  SchemeFrobeniusMap.openPullback_eq_of_commute _ _ (inclusion C)
    (traceOverlap_toLaurent C p base)

/-- Reciprocal trace frames differ by the signed degree twice p minus two input weight. -/
theorem traceFrame_reciprocal (base : RingSplitting C p) :
    ((laurentTrace base).toSpec (expChar_pos C p)).openPullback (inversion C) =
      ((laurentTrace base).toSpec (expChar_pos C p)).inputWeight
        ((Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv
          (LaurentPolynomial.C ((-1 : C) ^ (p - 1)) *
            LaurentPolynomial.T (2 * ((p : ℤ) - 1)))) := by
  let r : LaurentPolynomial C := LaurentPolynomial.C ((-1 : C) ^ (p - 1)) *
    LaurentPolynomial.T (2 * ((p : ℤ) - 1))
  have h : ((laurentTrace base).toSpec (expChar_pos C p)).openPullback (inversion C) =
      ((laurentTrace base).weight r).toSpec (expChar_pos C p) :=
    SchemeFrobeniusMap.openPullback_eq_of_commute _ _ (inversion C)
      (traceOverlap_reciprocal C p base)
  exact h.trans (traceWeight_toSpec (laurentTrace base) (expChar_pos C p) r)

end FrobeniusSplitting
