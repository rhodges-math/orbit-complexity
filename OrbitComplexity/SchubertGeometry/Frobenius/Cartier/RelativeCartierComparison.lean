import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator
import OrbitComplexity.SchubertGeometry.Frobenius.BkProjectiveCoefficients

/-! # The relative Cartier operator on the original section coordinates

The comparison uses the raw projections of the same matching line section.
Only the ground field is perfect; the coefficient ring has no perfectness or
reducedness assumption. The binomial coefficients are retained.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GroupActions FrobeniusSplitting Polynomial
noncomputable section
universe u v

namespace SchubertGeometry.ProjectiveCartier

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev indices := ULift.{u} (Fin 2)
private abbrev line (A : Type u) [CommRing A] := projectiveScheme A indices.{u}
private abbrev chartOpen (A : Type u) [CommRing A] (j : indices.{u}) :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule indices.{u} A) (MvPolynomial.X j)
private abbrev sectionLine (A : Type u) [CommRing A] (p : ℕ) :=
  SchubertGeometry.ProjectiveLine.projectiveTransitionModule A (2 * (p - 1))

private abbrev rawLeft {A : Type u} [CommRing A] {p : ℕ}
    (s : (sectionLine A p).val.obj (op ⊤)) : Polynomial A :=
  (Scheme.ΓSpecIso (.of (Polynomial A))).hom
    (((pullback.fst (SchubertGeometry.ProjectiveLine.leftRestriction A)
      (SchubertGeometry.ProjectiveLine.twistedRestriction A (2 * (p - 1)))).val.app (op ⊤)).hom s)

private abbrev rawRight {A : Type u} [CommRing A] {p : ℕ}
    (s : (sectionLine A p).val.obj (op ⊤)) : Polynomial A :=
  (Scheme.ΓSpecIso (.of (Polynomial A))).hom
    (((pullback.snd (SchubertGeometry.ProjectiveLine.leftRestriction A)
      (SchubertGeometry.ProjectiveLine.twistedRestriction A (2 * (p - 1)))).val.app (op ⊤)).hom s)

variable {K : Type v} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

/-- The operator of the original line section is the coefficient operator when
its two raw projections are the corresponding binomial-weighted monomials. -/
theorem relativeCartierOperator_eq_coefficient (ψ : FrobeniusLinearMap A p)
    (s : (sectionLine A p).val.obj (op ⊤)) (k : Fin p)
    (h0 : rawLeft s = C ((Nat.choose (p - 1) k : ℕ) : A) * X ^ (p - 1 - k))
    (h1 : rawRight s = C ((Nat.choose (p - 1) k : ℕ) : A) * X ^ (p - 1 + k)) :
    relativeCartierOperator (K := K) ψ s = projectiveLineCoeffOperator (K := K) ψ k := by
  symm
  unfold relativeCartierOperator
  apply SchemeFrobeniusMap.glue_unique
  intro j
  rw [projectiveLineCoeffOperator_chart]
  change (((polynomialTraceOfOperator (K := K) ψ).weight
      (C ((Nat.choose (p - 1) k : ℕ) : A) *
        X ^ (if j.down = 0 then p - 1 - k else p - 1 + k))).toSpec
          (expChar_pos K p)).pushforward (projectiveLinePolynomialIso A j).hom =
    (((polynomialTraceOfOperator (K := K) ψ).weight
      (if j.down = 0 then rawLeft s else rawRight s)).toSpec
        (expChar_pos K p)).pushforward (projectiveLinePolynomialIso A j).hom
  have hw : (if j.down = 0 then rawLeft s else rawRight s) =
      C ((Nat.choose (p - 1) k : ℕ) : A) *
        X ^ (if j.down = 0 then p - 1 - k else p - 1 + k) := by
    split_ifs
    · exact h0
    · exact h1
  rw [hw]

/-- The endpoint section after the infinity factor gives the normalized
zeroth member of the existing arbitrary-prior projective family. -/
theorem relativeCartierOperator_endpoint (ψ : FrobeniusLinearMap A p)
    (s : (sectionLine A p).val.obj (op ⊤))
    (h0 : rawLeft s = X ^ (p - 1)) (h1 : rawRight s = X ^ (p - 1)) :
    relativeCartierOperator (K := K) ψ s =
      projectiveLineCoeffOperator (K := K) ψ ⟨0, expChar_pos K p⟩ := by
  apply relativeCartierOperator_eq_coefficient
  · simpa only [Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, map_one, one_mul,
      Nat.sub_zero] using h0
  · simpa only [Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, map_one, one_mul,
      Nat.add_zero] using h1

end SchubertGeometry.ProjectiveCartier
