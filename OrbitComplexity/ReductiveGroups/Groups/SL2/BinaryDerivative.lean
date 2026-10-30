import OrbitComplexity.ReductiveGroups.Groups.SL2.BinaryParameters
import OrbitComplexity.ReductiveGroups.Groups.SL2.BinaryUpper
import OrbitComplexity.ReductiveGroups.Groups.SL2.BinaryExchange
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaMatrixDifferential
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Differential
import TauCeti.Algebra.Lie.Sl2.Standard

/-! # Derivatives of binary-form elementary subgroups -/

noncomputable section

namespace ReductiveGroups.BinaryForms

open TauCeti
open scoped Matrix

universe u
variable (R : Type u) [CommRing R]

private theorem upper_coefficient (n : ℕ) (i j : Fin (n + 1)) :
    (matrix (Polynomial R) n !![1, Polynomial.X; 0, 1] i j).coeff 1 =
      if (i : ℕ) + 1 = j then ((j : ℕ) : R) else 0 := by
  rw [matrix_upper]
  by_cases hle : (i : ℕ) ≤ j
  · rw [ite_eq_left hle]
    simp only [one_pow, mul_one]
    change (Polynomial.C (((j : ℕ).choose i : ℕ) : R) *
      Polynomial.X ^ ((j : ℕ) - i)).coeff 1 = _
    rw [Polynomial.coeff_C_mul_X_pow]
    by_cases h : (i : ℕ) + 1 = j
    · have hd : 1 = (j : ℕ) - i := by omega
      have hc : (j : ℕ).choose i = j := by
        rw [← h, Nat.choose_succ_self_right]
      rw [ite_eq_left hd, ite_eq_left h, hc]
    · have hd : 1 ≠ (j : ℕ) - i := by omega
      rw [ite_eq_right hd, ite_eq_right h]
  · rw [ite_eq_right hle]
    have h : (i : ℕ) + 1 ≠ j := by omega
    rw [ite_eq_right h]
    simp

private theorem lower_coefficient (n : ℕ) (i j : Fin (n + 1)) :
    (matrix (Polynomial R) n !![1, 0; Polynomial.X, 1] i j).coeff 1 =
      if (j : ℕ) + 1 = i then ((n - (j : ℕ) : ℕ) : R) else 0 := by
  have hs : !![0, 1; 1, 0] * !![1, Polynomial.X; 0, 1] *
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (Polynomial R)) =
        !![1, 0; Polynomial.X, 1] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [← hs, matrix_exchange_conjugate]
  have hi : (i.rev : ℕ) = n - i := by simp [Fin.val_rev]
  have hj : (j.rev : ℕ) = n - j := by simp [Fin.val_rev]
  have hiff : (i.rev : ℕ) + 1 = j.rev ↔ (j : ℕ) + 1 = i := by
    rw [hi, hj]
    have := i.isLt
    have := j.isLt
    omega
  rw [upper_coefficient]
  simp only [hiff]
  rw [hj]

variable (K : Type u) [Field K]

/-- The unit tangent of an elementary subgroup is its matrix unit in `sl₂`. -/
theorem root_tangent {i j : Fin 2} (hij : i ≠ j) :
    SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2
        (derivationComp (B := K)
          (SpecialLinear.rootSubgroupCoordinateMap (R := K) hij).hom
          (gaOriginDerivation K)) =
      LieAlgebra.SpecialLinear.single i j hij (1 : K) := by
  apply Subtype.ext
  rw [SpecialLinear.tangentLieEquivSl_apply, SpecialLinear.tangentMatrix_apply_coe,
    HopfIdeal.quotientLieHom_apply]
  change GeneralLinear.tangentMatrix 2
    (derivationComp (B := K) (SpecialLinear.coordinateMap K 2).hom
      (derivationComp (B := K)
        (SpecialLinear.rootSubgroupCoordinateMap (R := K) hij).hom
        (gaOriginDerivation K))) = Matrix.single i j 1
  have hcomp := LinearMap.congr_fun
    (derivationComp_comp (B := K)
      (SpecialLinear.rootSubgroupCoordinateMap (R := K) hij).hom
      (SpecialLinear.coordinateMap K 2).hom) (gaOriginDerivation K)
  rw [LinearMap.comp_apply] at hcomp
  rw [← hcomp]
  have heq : (SpecialLinear.rootSubgroupCoordinateMap (R := K) hij).hom.comp
      (SpecialLinear.coordinateMap K 2).hom =
        (GeneralLinear.rootSubgroupCoordinateMap (R := K) hij).hom :=
    congrArg (fun f => f.hom)
      (SpecialLinear.coordinateMap_comp_rootSubgroupCoordinateMap (R := K) hij)
  rw [heq, GeneralLinear.tangentMatrix_derivationComp_rootSubgroup,
    AdditiveGroup.gaTangentLinearEquiv_apply, gaOriginDerivation_generator]

/-- The upper elementary subgroup differentiates to the raising matrix. -/
theorem upper_differential (n : ℕ) (i j : Fin (n + 1)) :
    GeneralLinear.tangentMatrix (n + 1)
        (derivationComp (B := K) (rootCoordinateMap K n (zero_ne_one :
          (0 : Fin 2) ≠ 1)) (gaOriginDerivation K)) i j =
      if (i : ℕ) + 1 = j then ((j : ℕ) : K) else 0 := by
  rw [← GaMatrixPolynomial.coeff_one_differential]
  have hu : (1 : Matrix (Fin 2) (Fin 2) (Polynomial K)) +
      Matrix.single (0 : Fin 2) 1 Polynomial.X = !![1, Polynomial.X; 0, 1] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.single]
  simp only [gaMatrixPolynomial, rootCoordinateMap_polynomial, hu,
    matPolyEquiv_coeff_apply]
  exact upper_coefficient K n i j

/-- The lower elementary subgroup differentiates to the lowering matrix. -/
theorem lower_differential (n : ℕ) (i j : Fin (n + 1)) :
    GeneralLinear.tangentMatrix (n + 1)
        (derivationComp (B := K) (rootCoordinateMap K n (one_ne_zero :
          (1 : Fin 2) ≠ 0)) (gaOriginDerivation K)) i j =
      if (j : ℕ) + 1 = i then ((n - (j : ℕ) : ℕ) : K) else 0 := by
  rw [← GaMatrixPolynomial.coeff_one_differential]
  have hl : (1 : Matrix (Fin 2) (Fin 2) (Polynomial K)) +
      Matrix.single (1 : Fin 2) 0 Polynomial.X = !![1, 0; Polynomial.X, 1] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.single]
  simp only [gaMatrixPolynomial, rootCoordinateMap_polynomial, hl,
    matPolyEquiv_coeff_apply]
  exact lower_coefficient K n i j

end ReductiveGroups.BinaryForms
