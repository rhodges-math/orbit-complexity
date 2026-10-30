import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPoints
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Ga Invariant Subspace

Stability of an additive-group point from stability under its
matrix differential. -/

noncomputable section
namespace ReductiveGroups

variable {K : Type*} [Field K] [CharZero K]

/-- Finite exponential of a nilpotent matrix preserves every subspace
preserved by the matrix. -/
theorem matrixExponential_preserves_submodule (n : ℕ)
    (X : Matrix (Fin n) (Fin n) K) (hX : IsNilpotent X)
    (W : Submodule K (Fin n → K))
    (hW : ∀ v ∈ W, Matrix.toLin' X v ∈ W)
    (t : K) (v : Fin n → K) (hv : v ∈ W) :
    Matrix.toLin' (associativeExponential (K := K) (t • X)) v ∈ W := by
  let _ : Algebra ℚ K := (Rat.castHom K).toAlgebra
  let _ : Module ℚ (Matrix (Fin n) (Fin n) K) :=
    Module.compHom _ (algebraMap ℚ K)
  let _ : Module ℚ (Module.End K (Fin n → K)) :=
    Module.compHom _ (algebraMap ℚ K)
  let f : Matrix (Fin n) (Fin n) K →ₐ[K] Module.End K (Fin n → K) :=
    Matrix.toLinAlgEquiv'.toAlgHom
  have hmap : f (associativeExponential (K := K) (t • X)) =
      associativeExponential (K := K) (f (t • X)) :=
    IsNilpotent.map_exp ((hX.smul t)) f
  have hfW : ∀ w ∈ W, f (t • X) w ∈ W := by
    intro w hw
    change Matrix.toLin' (t • X) w ∈ W
    rw [map_smul]
    exact W.smul_mem t (hW w hw)
  have hpow : ∀ k : ℕ, ∀ w ∈ W, ((f (t • X)) ^ k) w ∈ W := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ', Module.End.mul_apply]
      exact hfW _ (ih w hw)
  obtain ⟨N, hN⟩ := hX.smul t
  change f (associativeExponential (K := K) (t • X)) v ∈ W
  rw [hmap]
  change IsNilpotent.exp (f (t • X)) v ∈ W
  rw [IsNilpotent.exp_eq_sum (show (f (t • X)) ^ N = 0 by
    rw [← map_pow, hN, map_zero])]
  simp only [LinearMap.sum_apply]
  exact W.sum_mem fun k hk => W.smul_mem _ (hpow k v hv)

/-- If the matrix differential of an original affine-group Ga morphism
preserves a subspace, every point of that Ga subgroup preserves it. -/
theorem GaAffineGroupMatrixPoint.preserves_of_tangent
    {B : Type*} [CommRing B] [HopfAlgebra K B]
    (n : ℕ) (x : B →ₐc[K] SymmetricAlgebra K K)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (W : Submodule K (Fin n → K))
    (hW : ∀ v ∈ W,
      Matrix.toLin' (affineGroupMatrixDifferential n ρ
        (gaAffineGroupTangent x)) v ∈ W)
    (t : K) (v : Fin n → K) (hv : v ∈ W) :
    Matrix.toLin'
      (↑(TauCeti.GeneralLinear.pointsMulEquiv n
        (TauCeti.AlgHom.mapDomain ρ
          (gaAffineGroupPoints x (Multiplicative.ofAdd t)))) :
            Matrix (Fin n) (Fin n) K) v ∈ W := by
  rw [GaAffineGroupPoints.matrix_eq_exponential n x ρ t]
  exact matrixExponential_preserves_submodule n
    (affineGroupMatrixDifferential n ρ (gaAffineGroupTangent x))
    (gaAffineGroupTangent_matrix_nilpotent n x ρ) W hW t v hv

end ReductiveGroups
