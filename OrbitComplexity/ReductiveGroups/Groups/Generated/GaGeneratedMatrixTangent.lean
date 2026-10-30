import OrbitComplexity.ReductiveGroups.Groups.Generated.GaGeneratedMatrixIdentity
import OrbitComplexity.ReductiveGroups.Groups.Tangents.ClosedSubgroupIntersectionTangent
import OrbitComplexity.ReductiveGroups.Groups.Representations.UpperMatrixGap

/-!
# Ga Generated Matrix Tangent

Linear matrix equations on generated points give exact linear
equations on the tangent of their closed generated subgroup. In particular,
unitriangular point equations imply strictly triangular tangent matrices. -/

noncomputable section
namespace ReductiveGroups

open TauCeti WithConv

universe u v
variable {K B : Type u} [Field K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] {ι : Type v}

/-- A matrix coordinate constant on all generated ground-field points has
zero differential on the tangent of their closed generated subgroup. -/
theorem GaGeneratedTangent.matrix_entry_eq_zero_of_points
    (x : ι → B →ₐc[K] SymmetricAlgebra K K) (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (i j : Fin n) (c : K)
    (hp : ∀ g : gaGeneratedPointSubgroup x,
      (GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g.val) :
        Matrix (Fin n) (Fin n) K) i j = c)
    (d : Derivation K B (Bialgebra.CounitAlgebra K B K))
    (hd : d ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of K B)
        (gaGeneratedHopfIdeal x)).hom).range) :
    affineGroupMatrixDifferential n ρ d i j = 0 := by
  have ha : ρ (GeneralLinear.genericMatrix K n i j) - algebraMap K B c ∈
      gaGeneratedHopfIdeal x := by
    rw [gaGeneratedHopfIdeal_eq_vanishingIdeal, HopfIdeal.mem_vanishingIdeal]
    intro g
    have hm := congrFun (congrFun
      (GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear n
        (g.val.ofConv.comp ρ.toAlgHom)) i) j
    change g.val.ofConv (ρ (GeneralLinear.genericMatrix K n i j)) =
      (GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g.val) :
        Matrix (Fin n) (Fin n) K) i j at hm
    change g.val.ofConv (ρ (GeneralLinear.genericMatrix K n i j) - algebraMap K B c) = 0
    rw [map_sub, AlgHom.commutes, hm, hp g]
    simp
  have hz := (tangent_mem_hopfQuotient_iff (gaGeneratedHopfIdeal x) d).mp hd _ ha
  have he := congrArg (Bialgebra.CounitAlgebra.algEquivSelf K B K) hz
  simp only [map_sub, Derivation.map_algebraMap, sub_zero, map_zero] at he
  rw [affineGroupMatrixDifferential_apply, GeneralLinear.tangentMatrix_apply,
    algEquivSelf_derivationComp_apply]
  exact he

/-- Upper-unitriangular equations on the generated points control the
closed subgroup tangent, including when the matrix size is zero. -/
theorem GaGeneratedTangent.matrixUpperGap_of_points
    (x : ι → B →ₐc[K] SymmetricAlgebra K K) (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hp : ∀ g : gaGeneratedPointSubgroup x,
      matrixUpperGap 1 ((GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g.val) :
        Matrix (Fin n) (Fin n) K) - 1))
    (d : Derivation K B (Bialgebra.CounitAlgebra K B K))
    (hd : d ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of K B)
        (gaGeneratedHopfIdeal x)).hom).range) :
    matrixUpperGap 1 (affineGroupMatrixDifferential n ρ d) := by
  intro i j hij
  apply GaGeneratedTangent.matrix_entry_eq_zero_of_points x n ρ i j
    ((1 : Matrix (Fin n) (Fin n) K) i j) _ d hd
  intro g
  exact sub_eq_zero.mp (hp g i j hij)

end ReductiveGroups
