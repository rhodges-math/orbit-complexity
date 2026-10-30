import OrbitComplexity.ReductiveGroups.Groups.SL2.BinaryDerivative
import Mathlib.Algebra.Lie.Matrix

/-! # The standard Lie representation of binary forms -/

noncomputable section

namespace ReductiveGroups.BinaryForms

open TauCeti
open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

universe u
variable (K : Type u) [Field K]

private def standardMatrixEquiv (n : ℕ) :
    Module.End K (Sl2Std K n) ≃ₗ⁅K⁆ Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  (LinearMap.toMatrixAlgEquiv (Sl2Std.basis K n)).toLieEquiv

/-- The differential of the algebraic binary-form representation, in standard `sl₂` coordinates. -/
private def lieRepresentation (n : ℕ) :
    SpecialLinear.sl (Fin 2) K →ₗ⁅K⁆ Module.End K (Sl2Std K n) :=
  (standardMatrixEquiv K n).symm.toLieHom.comp
    ((affineGroupMatrixDifferential (n + 1) (coordinateMap K n)).comp
      (TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm.toLieHom)

private theorem elementary_differential (n : ℕ) {i j : Fin 2} (hij : i ≠ j) :
    standardMatrixEquiv K n (lieRepresentation K n
      (SpecialLinear.single i j hij (1 : K))) =
        TauCeti.GeneralLinear.tangentMatrix (n + 1)
          (derivationComp (B := K) (rootCoordinateMap K n hij) (gaOriginDerivation K)) := by
  rw [← root_tangent K hij]
  change standardMatrixEquiv K n ((standardMatrixEquiv K n).symm
    (affineGroupMatrixDifferential (n + 1) (coordinateMap K n)
      ((TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm
        (TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2
          (derivationComp (B := K)
            (TauCeti.SpecialLinear.rootSubgroupCoordinateMap (R := K) hij).hom
            (gaOriginDerivation K)))))) = _
  rw [LieEquiv.symm_apply_apply, LieEquiv.apply_symm_apply,
    affineGroupMatrixDifferential_apply]
  have h := LinearMap.congr_fun
    (derivationComp_comp (B := K)
      (TauCeti.SpecialLinear.rootSubgroupCoordinateMap (R := K) hij).hom
      (coordinateMap K n)) (gaOriginDerivation K)
  rw [LinearMap.comp_apply] at h
  exact congrArg (TauCeti.GeneralLinear.tangentMatrix (n + 1)) h.symm

private theorem raise_matrix (n : ℕ) (i j : Fin (n + 1)) :
    standardMatrixEquiv K n (Sl2Std.raise K n) i j =
      if (i : ℕ) + 1 = j then ((j : ℕ) : K) else 0 := by
  simp only [standardMatrixEquiv, AlgEquiv.toLieEquiv_apply,
    LinearMap.toMatrixAlgEquiv_apply, Sl2Std.basis_repr_apply, Sl2Std.raise_apply]
  by_cases hi : (i : ℕ) < n
  · rw [dite_eq_left hi]
    simp only [Sl2Std.basis_apply, Fin.ext_iff]
    by_cases h : (i : ℕ) + 1 = j
    · rw [ite_eq_left h, ite_eq_left h, mul_one]
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun k : ℕ => (k : K)) h
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  · rw [dite_eq_right hi]
    have h : (i : ℕ) + 1 ≠ j := by omega
    rw [ite_eq_right h]

private theorem lower_matrix (n : ℕ) (i j : Fin (n + 1)) :
    standardMatrixEquiv K n (Sl2Std.lower K n) i j =
      if (j : ℕ) + 1 = i then ((n - (j : ℕ) : ℕ) : K) else 0 := by
  simp only [standardMatrixEquiv, AlgEquiv.toLieEquiv_apply,
    LinearMap.toMatrixAlgEquiv_apply, Sl2Std.basis_repr_apply, Sl2Std.lower_apply]
  by_cases hi : 0 < (i : ℕ)
  · rw [dite_eq_left hi]
    simp only [Sl2Std.basis_apply, Fin.ext_iff]
    by_cases h : (j : ℕ) + 1 = i
    · have hsub : (i : ℕ) - 1 = j := by omega
      rw [ite_eq_left hsub, ite_eq_left h, mul_one]
      have hj : (j : ℕ) ≤ n := by omega
      rw [Nat.cast_sub hj, ← h, Nat.cast_add, Nat.cast_one]
      ring
    · have hsub : (i : ℕ) - 1 ≠ j := by omega
      rw [ite_eq_right hsub, ite_eq_right h, mul_zero]
  · rw [dite_eq_right hi]
    have h : (j : ℕ) + 1 ≠ i := by omega
    rw [ite_eq_right h]

private theorem representation_raise (n : ℕ) :
    lieRepresentation K n (slFinTwoBasis K 0) = Sl2Std.raise K n := by
  apply (standardMatrixEquiv K n).injective
  change standardMatrixEquiv K n (lieRepresentation K n (slFinTwoBasis K 0)) =
    standardMatrixEquiv K n (Sl2Std.raise K n)
  rw [slFinTwoBasis_zero, elementary_differential]
  apply Matrix.ext
  intro i j
  rw [upper_differential, raise_matrix]

private theorem representation_lower (n : ℕ) :
    lieRepresentation K n (slFinTwoBasis K 1) = Sl2Std.lower K n := by
  apply (standardMatrixEquiv K n).injective
  change standardMatrixEquiv K n (lieRepresentation K n (slFinTwoBasis K 1)) =
    standardMatrixEquiv K n (Sl2Std.lower K n)
  rw [slFinTwoBasis_one, elementary_differential]
  apply Matrix.ext
  intro i j
  rw [lower_differential, lower_matrix]

/-- Differentiation of the algebraic degree-`n` representation gives the standard Lie module. -/
private theorem lieRepresentation_eq (n : ℕ) : lieRepresentation K n = Sl2Std.rep K n := by
  have hb (j : Fin 3) :
      lieRepresentation K n (slFinTwoBasis K j) = Sl2Std.rep K n (slFinTwoBasis K j) := by
    rw [Sl2Std.rep_apply_basis]
    fin_cases j
    · exact representation_raise K n
    · exact representation_lower K n
    · change lieRepresentation K n (slFinTwoBasis K 2) = Sl2Std.diag K n
      rw [← lie_slFinTwoBasis_zero_one, LieHom.map_lie,
        representation_raise, representation_lower, Sl2Std.lie_raise_lower]
  apply DFunLike.ext
  intro x
  rw [← (slFinTwoBasis K).sum_repr x]
  simp only [map_sum, map_smulₛₗ, RingHom.id_apply]
  exact Finset.sum_congr rfl fun j _ =>
    congrArg (fun T : Module.End K (Sl2Std K n) => (slFinTwoBasis K).repr x j • T) (hb j)

/-- The algebraic binary-form representation differentiates to the standard `sl₂` module. -/
theorem coordinateMap_differential (n : ℕ) (x : SpecialLinear.sl (Fin 2) K) :
    affineGroupMatrixDifferential (n + 1) (coordinateMap K n)
        ((TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm x) =
      LinearMap.toMatrix (Sl2Std.basis K n) (Sl2Std.basis K n) (Sl2Std.rep K n x) := by
  have h := congrArg (fun f : SpecialLinear.sl (Fin 2) K →ₗ⁅K⁆ Module.End K (Sl2Std K n) =>
      standardMatrixEquiv K n (f x)) (lieRepresentation_eq K n)
  change standardMatrixEquiv K n ((standardMatrixEquiv K n).symm
      (affineGroupMatrixDifferential (n + 1) (coordinateMap K n)
        ((TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm x))) = _ at h
  rw [LieEquiv.apply_symm_apply] at h
  exact h

end ReductiveGroups.BinaryForms
