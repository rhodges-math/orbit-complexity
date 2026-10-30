import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.HopfAlgebra
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# GL Coordinate Truncation

Finite-dimensional numerator-degree pieces of the coordinate Hopf algebra of GL. -/

noncomputable section
namespace ReductiveGroups

variable {K : Type*} [Field K] (n : ℕ)

private abbrev MatrixPolynomial := MvPolynomial (Fin n × Fin n) K

/-- Matrix-entry polynomials of total degree at most `d`. -/
def glPolynomialDegreeLE (d : ℕ) : Submodule K (MatrixPolynomial (K := K) n) where
  carrier := {p | p.totalDegree ≤ d}
  zero_mem' := by simp [MvPolynomial.totalDegree_zero]
  add_mem' := by
    intro p q hp hq
    exact (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)
  smul_mem' := by
    intro c p hp
    exact (MvPolynomial.totalDegree_smul_le c p).trans hp

/-- The equivalence is

```lean
p ∈ glPolynomialDegreeLE (K := K) n d ↔ p.totalDegree ≤ d
```
-/
theorem mem_glPolynomialDegreeLE (d : ℕ) (p : MatrixPolynomial (K := K) n) :
    p ∈ glPolynomialDegreeLE (K := K) n d ↔ p.totalDegree ≤ d := Iff.rfl

private theorem glPolynomialDegreeLE_eq_span (d : ℕ) :
    glPolynomialDegreeLE (K := K) n d =
      Submodule.span K {p : MatrixPolynomial (K := K) n |
        ∃ m : (Fin n × Fin n) →₀ ℕ,
          m.degree ≤ d ∧ p = MvPolynomial.monomial m 1} := by
  apply le_antisymm
  · intro p hp
    rw [MvPolynomial.as_sum p]
    apply Submodule.sum_mem
    intro m hm
    have hmdeg : m.degree ≤ d :=
      (MvPolynomial.le_totalDegree hm).trans hp
    have hmono : (MvPolynomial.monomial m (1 : K)) ∈
        Submodule.span K {q : MatrixPolynomial (K := K) n |
          ∃ m : (Fin n × Fin n) →₀ ℕ,
            m.degree ≤ d ∧ q = MvPolynomial.monomial m 1} :=
      Submodule.subset_span ⟨m, hmdeg, rfl⟩
    simpa [MvPolynomial.smul_monomial] using
      (Submodule.smul_mem _ (p.coeff m) hmono)
  · apply Submodule.span_le.mpr
    rintro p ⟨m, hm, rfl⟩
    change (MvPolynomial.monomial m (1 : K)).totalDegree ≤ d
    simpa [MvPolynomial.totalDegree_monomial, Finsupp.degree_apply, Finsupp.sum] using hm

/-- Every polynomial total-degree piece is finite-dimensional over the field. -/
theorem glPolynomialDegreeLE_finite (d : ℕ) :
    Module.Finite K (glPolynomialDegreeLE (K := K) n d) := by
  rw [glPolynomialDegreeLE_eq_span]
  apply Module.Finite.span_of_finite K
  have hfinite : ({m : (Fin n × Fin n) →₀ ℕ | m.degree ≤ d} : Set _).Finite :=
    Finsupp.finite_of_degree_le d
  simpa [Set.image, eq_comm] using
    hfinite.image (fun m => MvPolynomial.monomial m (1 : K))

private abbrev determinantPolynomial : MatrixPolynomial (K := K) n :=
  Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K)

private abbrev determinantInverse : TauCeti.GeneralLinear.CoordinateRing K n :=
  IsLocalization.Away.invSelf (determinantPolynomial (K := K) n)

/-- The numerator-degree `d`, denominator-power `r` piece, inside the coordinate Hopf
algebra. The image construction does not assume that localization is injective. -/
def glCoordinateTruncation (r d : ℕ) :
    Submodule K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) :=
  LinearMap.range <|
    (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n).toLinearEquiv.toLinearMap |>.comp
      ((LinearMap.mulRight K ((determinantInverse (K := K) n) ^ r)).comp
        ((TauCeti.GeneralLinear.coordinateRingMap K n).toLinearMap.comp
          (glPolynomialDegreeLE (K := K) n d).subtype))

/-- Each numerator-degree and denominator-power piece is finite-dimensional. -/
theorem glCoordinateTruncation_finite (r d : ℕ) :
    Module.Finite K (glCoordinateTruncation (K := K) n r d) := by
  unfold glCoordinateTruncation
  let f :=
    (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n).toLinearEquiv.toLinearMap |>.comp
      ((LinearMap.mulRight K ((determinantInverse (K := K) n) ^ r)).comp
        ((TauCeti.GeneralLinear.coordinateRingMap K n).toLinearMap.comp
          (glPolynomialDegreeLE (K := K) n d).subtype))
  change Module.Finite K f.range
  have : Module.Finite K (glPolynomialDegreeLE (K := K) n d) :=
    glPolynomialDegreeLE_finite n d
  apply Module.Finite.of_surjective f.rangeRestrict
  rintro ⟨x, ⟨a, ha⟩⟩
  exact ⟨a, Subtype.ext ha⟩

/-- The finite-dimensional pieces exhaust every coordinate of the `GLₙ` Hopf algebra. -/
theorem glCoordinateTruncation_exhaustive
    (b : TauCeti.GeneralLinear.coordinateHopfAlgebra K n) :
    ∃ r d : ℕ, b ∈ glCoordinateTruncation (K := K) n r d := by
  let z : TauCeti.GeneralLinear.CoordinateRing K n :=
    (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n).symm b
  let a := (IsLocalization.Away.sec (determinantPolynomial (K := K) n) z).1
  let r := (IsLocalization.Away.sec (determinantPolynomial (K := K) n) z).2
  let d := a.totalDegree
  refine ⟨r, d, ?_⟩
  have ha : a ∈ glPolynomialDegreeLE (K := K) n d := by
    change a.totalDegree ≤ d
    rfl
  let p : glPolynomialDegreeLE (K := K) n d := ⟨a, ha⟩
  have hunit : TauCeti.GeneralLinear.coordinateRingMap K n
      (determinantPolynomial (K := K) n) * determinantInverse (K := K) n = 1 := by
    exact IsLocalization.Away.mul_invSelf _
  have hpow : TauCeti.GeneralLinear.coordinateRingMap K n
      ((determinantPolynomial (K := K) n) ^ r) *
        (determinantInverse (K := K) n) ^ r = 1 := by
    rw [map_pow, ← mul_pow, hunit, one_pow]
  have hz : z = TauCeti.GeneralLinear.coordinateRingMap K n a *
      (determinantInverse (K := K) n) ^ r := by
    calc
      z = z * 1 := (mul_one z).symm
      _ = z * (TauCeti.GeneralLinear.coordinateRingMap K n
        ((determinantPolynomial (K := K) n) ^ r) *
          (determinantInverse (K := K) n) ^ r) := by rw [hpow]
      _ = (z * TauCeti.GeneralLinear.coordinateRingMap K n
        ((determinantPolynomial (K := K) n) ^ r)) *
          (determinantInverse (K := K) n) ^ r := by ring
      _ = TauCeti.GeneralLinear.coordinateRingMap K n a *
          (determinantInverse (K := K) n) ^ r := by
            rw [TauCeti.GeneralLinear.coordinateRingMap_apply]
            rw [IsLocalization.Away.sec_spec (determinantPolynomial (K := K) n) z]
            rfl
  change ∃ p : glPolynomialDegreeLE (K := K) n d,
    ((TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n).toLinearEquiv.toLinearMap).comp
        ((LinearMap.mulRight K ((determinantInverse (K := K) n) ^ r)).comp
          ((TauCeti.GeneralLinear.coordinateRingMap K n).toLinearMap.comp
            (glPolynomialDegreeLE (K := K) n d).subtype)) p = b
  refine ⟨p, ?_⟩
  change TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
    (TauCeti.GeneralLinear.coordinateRingMap K n a *
      (determinantInverse (K := K) n) ^ r) = b
  rw [← hz]
  exact (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n).apply_symm_apply b

end ReductiveGroups
