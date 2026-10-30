import OrbitComplexity.FrobeniusSplitting.Splittings.LaurentOperators
import OrbitComplexity.SchubertGeometry.Frobenius.ProjectiveOperators


/-! # Global Cartier operators on the projective line -/

namespace SchubertGeometry
open AlgebraicGeometry CategoryTheory Opposite GroupActions FrobeniusSplitting Polynomial
noncomputable section
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev lineIndex : Type u := ULift.{u} (Fin 2)
private abbrev lineOpen (A : Type u) [CommRing A] (j : lineIndex.{u}) :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule lineIndex.{u} A) (MvPolynomial.X j)

variable {K : Type v} {A : Type u} [Field K] {p : ℕ} [ExpChar K p]
  [PerfectRing K p] [CommRing A] [Algebra K A]

private theorem coefficient_toLaurent (ψ : FrobeniusLinearMap A p) (c : A) (m : ℕ)
    (f : Polynomial A) :
    laurentTraceOfOperator (K := K) ψ
        (LaurentPolynomial.C c * LaurentPolynomial.T (m : ℤ) * f.toLaurent) =
      (polynomialTraceOfOperator (K := K) ψ (C c * X ^ m * f)).toLaurent := by
  rw [← laurentOperator_toLaurent]
  congr 1
  simp only [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]

private theorem weighted_reciprocal (ψ : FrobeniusLinearMap A p) (c : A) (m n : ℕ)
    (hmn : m + n = 2 * (p - 1)) (f : LaurentPolynomial A) :
    laurentTraceOfOperator (K := K) ψ
        (LaurentPolynomial.C c * LaurentPolynomial.T (m : ℤ) * LaurentPolynomial.invert f) =
      LaurentPolynomial.invert
        (laurentTraceOfOperator (K := K) ψ
          (LaurentPolynomial.C c * LaurentPolynomial.T (n : ℤ) * f)) := by
  have hexp : 2 * ((p : ℤ) - 1) + -(n : ℤ) = (m : ℤ) := by
    have hp := expChar_pos K p
    have hcast := congrArg (fun q : ℕ => (q : ℤ)) hmn
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hp,
      Nat.cast_one] at hcast
    omega
  rw [← laurentOperator_invert]
  congr 1
  simp only [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
  calc
    _ = LaurentPolynomial.C c *
        (LaurentPolynomial.T (2 * ((p : ℤ) - 1)) * LaurentPolynomial.T (-(n : ℤ))) *
        LaurentPolynomial.invert f := by rw [← LaurentPolynomial.T_add, hexp]
    _ = _ := by ac_rfl

private theorem coefficient_reciprocal (ψ : FrobeniusLinearMap A p) (j : Fin p)
    (f : Polynomial A) :
    laurentTraceOfOperator (K := K) ψ
        (LaurentPolynomial.C ((Nat.choose (p - 1) j : ℕ) : A) *
          LaurentPolynomial.T ((p - 1 - j : ℕ) : ℤ) *
          LaurentPolynomial.invert f.toLaurent) =
      LaurentPolynomial.invert
        (polynomialTraceOfOperator (K := K) ψ
          (C ((Nat.choose (p - 1) j : ℕ) : A) * X ^ (p - 1 + j) * f)).toLaurent := by
  rw [weighted_reciprocal (K := K) ψ _ (p - 1 - j) (p - 1 + j)]
  · rw [coefficient_toLaurent]
  · have hj := j.isLt
    omega

private def chartOperator (ψ : FrobeniusLinearMap A p) (k : Fin p) (j : lineIndex.{u}) :
    FrobeniusLinearMap (Polynomial A) p :=
  (polynomialTraceOfOperator (K := K) ψ).weight
    (C ((Nat.choose (p - 1) k : ℕ) : A) *
      X ^ (if j.down = 0 then p - 1 - k else p - 1 + k))

private def chartSheafOperator (ψ : FrobeniusLinearMap A p) (k : Fin p) (j : lineIndex.{u}) :
    SchemeFrobeniusMap (lineOpen A j).toScheme p :=
  ((chartOperator (K := K) ψ k j).toSpec (expChar_pos K p)).pushforward
    (projectiveLinePolynomialIso A j).hom

private def overlapOperator (ψ : FrobeniusLinearMap A p) (k : Fin p) :
    FrobeniusLinearMap (LaurentPolynomial A) p :=
  (laurentTraceOfOperator (K := K) ψ).weight
    (LaurentPolynomial.C ((Nat.choose (p - 1) k : ℕ) : A) *
      LaurentPolynomial.T ((p - 1 - k : ℕ) : ℤ))

private theorem chart_cross (ψ : FrobeniusLinearMap A p) (k : Fin p)
    (V : (projectiveScheme A lineIndex.{u}).Opens)
    (hV : V ≤ lineOpen A ⟨0⟩) (hV' : V ≤ lineOpen A ⟨1⟩) :
    (chartSheafOperator (K := K) ψ k ⟨0⟩).onSubopen V hV =
      (chartSheafOperator (K := K) ψ k ⟨1⟩).onSubopen V hV' := by
  let a : Spec (.of (LaurentPolynomial A)) ⟶ Spec (.of (Polynomial A)) :=
    Spec.map (CommRingCat.ofHom Polynomial.toLaurent)
  let b : Spec (.of (LaurentPolynomial A)) ⟶ Spec (.of (Polynomial A)) :=
    Spec.map (CommRingCat.ofHom
      ((LaurentPolynomial.invert : LaurentPolynomial A ≃ₐ[A] LaurentPolynomial A).toRingHom.comp
        Polynomial.toLaurent))
  have : IsOpenImmersion a :=
    IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial A)
  have ha (W : (Spec (.of (Polynomial A))).Opens) (s : Γ(Spec (.of (Polynomial A)), W)) :
      ((overlapOperator (K := K) ψ k).toSpec (expChar_pos K p)).onOpen (a ⁻¹ᵁ W) (a.app W s) =
        a.app W (((chartOperator (K := K) ψ k ⟨0⟩).toSpec (expChar_pos K p)).onOpen W s) := by
    apply (chartOperator (K := K) ψ k ⟨0⟩).toSpec_naturality (overlapOperator (K := K) ψ k)
      (expChar_pos K p) Polynomial.toLaurent _ W s
    intro f
    change laurentTraceOfOperator (K := K) ψ
      (LaurentPolynomial.C ((Nat.choose (p - 1) k : ℕ) : A) *
        LaurentPolynomial.T ((p - 1 - k : ℕ) : ℤ) * f.toLaurent) = _
    simpa only [chartOperator, ↓reduceIte, FrobeniusLinearMap.weight_apply] using
      coefficient_toLaurent (K := K) ψ ((Nat.choose (p - 1) k : ℕ) : A) (p - 1 - k) f
  have hb (W : (Spec (.of (Polynomial A))).Opens) (s : Γ(Spec (.of (Polynomial A)), W)) :
      ((overlapOperator (K := K) ψ k).toSpec (expChar_pos K p)).onOpen (b ⁻¹ᵁ W) (b.app W s) =
        b.app W (((chartOperator (K := K) ψ k ⟨1⟩).toSpec (expChar_pos K p)).onOpen W s) := by
    apply (chartOperator (K := K) ψ k ⟨1⟩).toSpec_naturality (overlapOperator (K := K) ψ k)
      (expChar_pos K p) _ _ W s
    intro f
    change laurentTraceOfOperator (K := K) ψ
      (LaurentPolynomial.C ((Nat.choose (p - 1) k : ℕ) : A) *
        LaurentPolynomial.T ((p - 1 - k : ℕ) : ℤ) *
        LaurentPolynomial.invert f.toLaurent) =
      LaurentPolynomial.invert ((chartOperator (K := K) ψ k ⟨1⟩ f).toLaurent)
    simpa only [chartOperator, show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte,
      FrobeniusLinearMap.weight_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_toRingEquiv] using
        coefficient_reciprocal (K := K) ψ k f
  apply SchemeFrobeniusMap.chartFormula_eq (lineOpen A ⟨0⟩) (lineOpen A ⟨1⟩)
    (projectiveLinePolynomialIso A ⟨0⟩) (projectiveLinePolynomialIso A ⟨1⟩)
    ((chartOperator (K := K) ψ k ⟨0⟩).toSpec (expChar_pos K p))
    ((chartOperator (K := K) ψ k ⟨1⟩).toSpec (expChar_pos K p))
    ((overlapOperator (K := K) ψ k).toSpec (expChar_pos K p)) a b ha hb
    (projectiveLinePolynomial_overlap A) V hV hV'
  exact (le_inf hV hV').trans (projectiveLinePolynomial_inter A).symm.le

private theorem chart_compatible (ψ : FrobeniusLinearMap A p) (k : Fin p)
    (i j : lineIndex.{u}) (V : (projectiveScheme A lineIndex.{u}).Opens)
    (hi : V ≤ lineOpen A i) (hj : V ≤ lineOpen A j) :
    (chartSheafOperator (K := K) ψ k i).onSubopen V hi =
      (chartSheafOperator (K := K) ψ k j).onSubopen V hj := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j
  · rfl
  · exact chart_cross (K := K) ψ k V hi hj
  · exact (chart_cross (K := K) ψ k V hj hi).symm
  · rfl

private theorem lineOpen_cover : (⨆ j : lineIndex.{u}, lineOpen A j) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule lineIndex.{u} A)
    (MvPolynomial.X : lineIndex.{u} → MvPolynomial lineIndex.{u} A)
      (projective_irrelevant_eq_span A lineIndex.{u}).le

/-- The rank-one binomial coefficients define global Frobenius-linear sheaf operators. -/
def projectiveLineCoeffOperator (ψ : FrobeniusLinearMap A p) (k : Fin p) :
    SchemeFrobeniusMap (projectiveScheme A (ULift.{u} (Fin 2))) p :=
  SchemeFrobeniusMap.glue (lineOpen A) (chartSheafOperator (K := K) ψ k)
    (chart_compatible (K := K) ψ k) lineOpen_cover

/-- Restriction to either polynomial chart gives its complementary Cartier-trace weight. -/
theorem projectiveLineCoeffOperator_chart (ψ : FrobeniusLinearMap A p) (k : Fin p)
    (j : ULift.{u} (Fin 2)) :
    (projectiveLineCoeffOperator (K := K) ψ k).restrict
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) A)
          (MvPolynomial.X j)) =
      (((polynomialTraceOfOperator (K := K) ψ).weight
        (C ((Nat.choose (p - 1) k : ℕ) : A) *
          X ^ (if j.down = 0 then p - 1 - k else p - 1 + k))).toSpec
            (expChar_pos K p)).pushforward (projectiveLinePolynomialIso A j).hom :=
  SchemeFrobeniusMap.glue_restrict _ _ _ _ j


/-- A normalized coefficient operator recovers the existing global binomial family. -/
theorem projectiveLineCoeffOperator_normalized [ExpChar A p] (base : RingSplitting A p)
    (k : Fin p) :
    projectiveLineCoeffOperator (K := K) base.toOperator k =
      projectiveLineCanonicalOperator base k := by
  symm
  unfold projectiveLineCoeffOperator
  apply SchemeFrobeniusMap.glue_unique
  intro j
  rw [projectiveLineCanonicalOperator_chart]
  simp only [chartSheafOperator, chartOperator, polynomialTraceOfOperator_normalized]

end
end SchubertGeometry
