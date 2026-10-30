import OrbitComplexity.ReductiveGroups.Groups.Generated.GaGeneratedMatrixTangent
import OrbitComplexity.ReductiveGroups.Groups.Solvable.SolvableGaMatrixUnipotence

/-!
# Ga Generated Triangular Tangent

Ga tangents upper triangular in one representation generate a
subgroup with unitriangular points and strictly triangular tangent image. -/

noncomputable section
namespace ReductiveGroups

open TauCeti WithConv

universe u v
variable {K B : Type u} [Field K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] {ι : Type v}

omit [CharZero K] in
private theorem matrixUpperGap_mul_sub_one {n : ℕ}
    {A C : Matrix (Fin n) (Fin n) K}
    (hA : matrixUpperGap 1 (A - 1)) (hC : matrixUpperGap 1 (C - 1)) :
    matrixUpperGap 1 (A * C - 1) := by
  have hi : A * C - 1 = (A - 1) + (C - 1) + (A - 1) * (C - 1) := by
    noncomm_ring
  rw [hi]
  have hp := matrixUpperGap_mono (matrixUpperGap_mul hA hC) (by omega : 1 ≤ 1 + 1)
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hC i j hij, hp i j hij, add_zero]

/-- All generated points are unitriangular when the generating
tangents are upper triangular in the same fixed representation. -/
theorem GaGeneratedPoint.matrixUpperGap_of_tangents_upper
    (x : ι → B →ₐc[K] SymmetricAlgebra K K) (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hX : ∀ i, matrixUpperGap 0 (affineGroupMatrixDifferential n ρ (gaAffineGroupTangent (x i))))
    (g : gaGeneratedPointSubgroup x) :
    matrixUpperGap 1 ((GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g.val) :
      Matrix (Fin n) (Fin n) K) - 1) := by
  let F : WithConv (B →ₐ[K] K) →* (Matrix (Fin n) (Fin n) K)ˣ :=
    (GeneralLinear.pointsMulEquiv (R := K) (A := K) n).toMonoidHom.comp
      (AlgHom.mapDomain ρ)
  have hgen (i : ι) (t : Multiplicative K) :
      matrixUpperGap 1 ((F (gaAffineGroupPoints (x i) t) : Matrix (Fin n) (Fin n) K) - 1) := by
    let D := affineGroupMatrixDifferential n ρ (gaAffineGroupTangent (x i))
    have hnil : IsNilpotent D := gaAffineGroupTangent_matrix_nilpotent n (x i) ρ
    have hu : matrixUpperGap 1 D := matrixUpperGap_one_of_nilpotent_upper (hX i) hnil
    have hscaled : matrixUpperGap 1 (t.toAdd • D) := by
      intro a b hab
      simp only [Matrix.smul_apply, hu a b hab, smul_zero]
    have hpoint := GaAffineGroupPoints.matrix_eq_exponential n (x i) ρ t.toAdd
    change matrixUpperGap 1 ((GeneralLinear.pointsMulEquiv n
      (AlgHom.mapDomain ρ (gaAffineGroupPoints (x i) t)) : Matrix (Fin n) (Fin n) K) - 1)
    simp only [ofAdd_toAdd] at hpoint
    rw [hpoint]
    exact matrixUpperGap_exp_sub_one hscaled (hnil.smul t.toAdd)
  have hclosure : ∀ a ∈ gaGeneratedPointSubgroup x,
      matrixUpperGap 1 ((F a : Matrix (Fin n) (Fin n) K) - 1) := by
    intro a ha
    change a ∈ Subgroup.closure (⋃ i : ι, Set.range (gaAffineGroupPoints (x i))) at ha
    induction ha using Subgroup.closure_induction'' with
    | mem a ha =>
        obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp ha
        exact hgen i t
    | inv_mem a ha =>
        obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp ha
        rw [← map_inv (gaAffineGroupPoints (x i)) t]
        exact hgen i t⁻¹
    | one =>
        simp only [map_one, Units.val_one, sub_self]
        intro i j hij
        rfl
    | mul a b _ _ ha hb =>
        simpa only [map_mul, Units.val_mul] using matrixUpperGap_mul_sub_one ha hb
  exact hclosure g.val g.property

/-- The closed generated subgroup inherits strictly triangular tangent
matrices; it is not merely the abstract subgroup of generated points. -/
theorem GaGeneratedTangent.matrixUpperGap_of_tangents_upper
    (x : ι → B →ₐc[K] SymmetricAlgebra K K) (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hX : ∀ i, matrixUpperGap 0 (affineGroupMatrixDifferential n ρ (gaAffineGroupTangent (x i))))
    (d : Derivation K B (Bialgebra.CounitAlgebra K B K))
    (hd : d ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of K B)
        (gaGeneratedHopfIdeal x)).hom).range) :
    matrixUpperGap 1 (affineGroupMatrixDifferential n ρ d) :=
  GaGeneratedTangent.matrixUpperGap_of_points x n ρ
    (GaGeneratedPoint.matrixUpperGap_of_tangents_upper x n ρ hX) d hd

end ReductiveGroups
