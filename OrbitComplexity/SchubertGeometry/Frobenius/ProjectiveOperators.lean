import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorComparison
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorNormalization
import OrbitComplexity.FrobeniusSplitting.Splittings.CartierCovariance
import OrbitComplexity.SchubertGeometry.Frobenius.ProjectiveLine

/-! # Global Cartier operators on the projective line -/

namespace SchubertGeometry
open AlgebraicGeometry CategoryTheory Opposite GroupActions FrobeniusSplitting Polynomial
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev lineIndex : Type u := ULift.{u} (Fin 2)
private abbrev lineOpen (R : Type u) [CommRing R] (j : lineIndex.{u}) :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule lineIndex.{u} R) (MvPolynomial.X j)

variable {R : Type u} [CommRing R] {p : ℕ} [ExpChar R p]

private def chartOperator (base : RingSplitting R p) (k : Fin p) (j : lineIndex.{u}) :
    FrobeniusLinearMap (Polynomial R) p :=
  (univariateTrace base).weight
    (C ((Nat.choose (p - 1) k : ℕ) : R) *
      X ^ (if j.down = 0 then p - 1 - k else p - 1 + k))

private def chartSheafOperator (base : RingSplitting R p) (k : Fin p) (j : lineIndex.{u}) :
    SchemeFrobeniusMap (lineOpen R j).toScheme p :=
  ((chartOperator base k j).toSpec (expChar_pos R p)).pushforward
    (projectiveLinePolynomialIso R j).hom

private def overlapOperator (base : RingSplitting R p) (k : Fin p) :
    FrobeniusLinearMap (LaurentPolynomial R) p :=
  (laurentTrace base).weight
    (LaurentPolynomial.C ((Nat.choose (p - 1) k : ℕ) : R) *
      LaurentPolynomial.T ((p - 1 - k : ℕ) : ℤ))

private theorem chart_cross (base : RingSplitting R p) (k : Fin p)
    (V : (projectiveScheme R lineIndex.{u}).Opens)
    (hV : V ≤ lineOpen R ⟨0⟩) (hV' : V ≤ lineOpen R ⟨1⟩) :
    (chartSheafOperator base k ⟨0⟩).onSubopen V hV =
      (chartSheafOperator base k ⟨1⟩).onSubopen V hV' := by
  let a : Spec (.of (LaurentPolynomial R)) ⟶ Spec (.of (Polynomial R)) :=
    Spec.map (CommRingCat.ofHom Polynomial.toLaurent)
  let b : Spec (.of (LaurentPolynomial R)) ⟶ Spec (.of (Polynomial R)) :=
    Spec.map (CommRingCat.ofHom
      ((LaurentPolynomial.invert : LaurentPolynomial R ≃ₐ[R] LaurentPolynomial R).toRingHom.comp
        Polynomial.toLaurent))
  have : IsOpenImmersion a :=
    IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial R)
  have ha (W : (Spec (.of (Polynomial R))).Opens) (s : Γ(Spec (.of (Polynomial R)), W)) :
      ((overlapOperator base k).toSpec (expChar_pos R p)).onOpen (a ⁻¹ᵁ W) (a.app W s) =
        a.app W (((chartOperator base k ⟨0⟩).toSpec (expChar_pos R p)).onOpen W s) := by
    apply (chartOperator base k ⟨0⟩).toSpec_naturality (overlapOperator base k)
      (expChar_pos R p) Polynomial.toLaurent _ W s
    intro f
    change laurentTrace base
      (LaurentPolynomial.C ((Nat.choose (p - 1) k : ℕ) : R) *
        LaurentPolynomial.T ((p - 1 - k : ℕ) : ℤ) * f.toLaurent) = _
    simpa only [chartOperator, ↓reduceIte, FrobeniusLinearMap.weight_apply] using
      weightedTrace_toLaurent base ((Nat.choose (p - 1) k : ℕ) : R) (p - 1 - k) f
  have hb (W : (Spec (.of (Polynomial R))).Opens) (s : Γ(Spec (.of (Polynomial R)), W)) :
      ((overlapOperator base k).toSpec (expChar_pos R p)).onOpen (b ⁻¹ᵁ W) (b.app W s) =
        b.app W (((chartOperator base k ⟨1⟩).toSpec (expChar_pos R p)).onOpen W s) := by
    apply (chartOperator base k ⟨1⟩).toSpec_naturality (overlapOperator base k)
      (expChar_pos R p) _ _ W s
    intro f
    change laurentTrace base
      (LaurentPolynomial.C ((Nat.choose (p - 1) k : ℕ) : R) *
        LaurentPolynomial.T ((p - 1 - k : ℕ) : ℤ) *
        LaurentPolynomial.invert f.toLaurent) =
      LaurentPolynomial.invert ((chartOperator base k ⟨1⟩ f).toLaurent)
    simpa only [chartOperator, show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte,
      FrobeniusLinearMap.weight_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_toRingEquiv] using
        canonicalTrace_reciprocal base k f
  apply SchemeFrobeniusMap.chartFormula_eq (lineOpen R ⟨0⟩) (lineOpen R ⟨1⟩)
    (projectiveLinePolynomialIso R ⟨0⟩) (projectiveLinePolynomialIso R ⟨1⟩)
    ((chartOperator base k ⟨0⟩).toSpec (expChar_pos R p))
    ((chartOperator base k ⟨1⟩).toSpec (expChar_pos R p))
    ((overlapOperator base k).toSpec (expChar_pos R p)) a b ha hb
    (projectiveLinePolynomial_overlap R) V hV hV'
  exact (le_inf hV hV').trans (projectiveLinePolynomial_inter R).symm.le

private theorem chart_compatible (base : RingSplitting R p) (k : Fin p)
    (i j : lineIndex.{u}) (V : (projectiveScheme R lineIndex.{u}).Opens)
    (hi : V ≤ lineOpen R i) (hj : V ≤ lineOpen R j) :
    (chartSheafOperator base k i).onSubopen V hi =
      (chartSheafOperator base k j).onSubopen V hj := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j
  · rfl
  · exact chart_cross base k V hi hj
  · exact (chart_cross base k V hj hi).symm
  · rfl

private theorem lineOpen_cover : (⨆ j : lineIndex.{u}, lineOpen R j) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule lineIndex.{u} R)
    (MvPolynomial.X : lineIndex.{u} → MvPolynomial lineIndex.{u} R)
      (projective_irrelevant_eq_span R lineIndex.{u}).le

/-- The rank-one binomial coefficients define global Frobenius-linear sheaf operators. -/
def projectiveLineCanonicalOperator (base : RingSplitting R p) (k : Fin p) :
    SchemeFrobeniusMap (projectiveScheme R (ULift.{u} (Fin 2))) p :=
  SchemeFrobeniusMap.glue (lineOpen R) (chartSheafOperator base k)
    (chart_compatible base k) lineOpen_cover

/-- Restriction to either polynomial chart gives its complementary Cartier-trace weight. -/
theorem projectiveLineCanonicalOperator_chart (base : RingSplitting R p) (k : Fin p)
    (j : ULift.{u} (Fin 2)) :
    (projectiveLineCanonicalOperator base k).restrict
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) R)
          (MvPolynomial.X j)) =
      (((univariateTrace base).weight
        (C ((Nat.choose (p - 1) k : ℕ) : R) *
          X ^ (if j.down = 0 then p - 1 - k else p - 1 + k))).toSpec
            (expChar_pos R p)).pushforward (projectiveLinePolynomialIso R j).hom :=
  SchemeFrobeniusMap.glue_restrict _ _ _ _ j

end
end SchubertGeometry

namespace SchubertGeometry
open AlgebraicGeometry CategoryTheory GroupActions FrobeniusSplitting Polynomial
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem standard_trace {R : Type*} [CommRing R] {p : ℕ} [ExpChar R p]
    (base : RingSplitting R p) :
    (univariateTrace base).weight (X ^ (p - 1)) = base.univariate.toOperator := by
  apply FrobeniusLinearMap.ext
  intro f
  apply Polynomial.ext
  intro n
  change (univariateTrace base (X ^ (p - 1) * f)).coeff n = (base.univariate f).coeff n
  rw [univariateTrace_coeff, coeff_X_pow_mul, RingSplitting.univariate_coeff]

private theorem forget_pushforward {X Y : Scheme.{u}} {p : ℕ}
    (splitting : SchemeSplitting X p) (f : X ⟶ Y) [IsIso f.c] :
    (splitting.pushforward f).toOperator = splitting.toOperator.pushforward f := rfl

/-- The zeroth global binomial operator is the normalized projective-line splitting. -/
theorem projectiveLineCanonicalOperator_zero {R : Type u} [CommRing R] {p : ℕ}
    [ExpChar R p] (base : RingSplitting R p) :
    projectiveLineCanonicalOperator base ⟨0, expChar_pos R p⟩ =
      (projectiveLineSplitting base).toOperator := by
  symm
  unfold projectiveLineCanonicalOperator
  apply SchemeFrobeniusMap.glue_unique
  intro j
  change ((projectiveLineSplitting base).restrict _).toOperator = _
  unfold projectiveLineSplitting
  rw [SchemeSplitting.glue_restrict]
  change ((base.univariate.toSpec (expChar_pos R p)).pushforward
      (projectiveLinePolynomialIso R j).hom).toOperator =
    (((univariateTrace base).weight
      (C ((Nat.choose (p - 1) 0 : ℕ) : R) *
        X ^ (if j.down = 0 then p - 1 - 0 else p - 1 + 0))).toSpec
          (expChar_pos R p)).pushforward (projectiveLinePolynomialIso R j).hom
  simp only [Nat.choose_zero_right, Nat.cast_one, map_one, one_mul, Nat.sub_zero,
    Nat.add_zero, ite_self]
  rw [forget_pushforward, RingSplitting.toOperator_toSpec, standard_trace]

end
end SchubertGeometry
