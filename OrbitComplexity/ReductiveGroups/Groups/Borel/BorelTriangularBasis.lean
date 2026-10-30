import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTorusUnipotentMatrix
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTorusUnipotentCharacters
import OrbitComplexity.ReductiveGroups.Groups.Representations.MatrixInvariantFlags
import OrbitComplexity.ReductiveGroups.Groups.Solvable.SolvableLieTriangularBasis
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootGeneration
import OrbitComplexity.ReductiveGroups.Groups.Solvable.ConnectedGeneratedPointClosure
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootPointUnipotence
import OrbitComplexity.ReductiveGroups.Groups.Borel.PointBasis

/-! # Triangularizing a Borel tangent algebra and its root-unipotent subgroup -/

noncomputable section
namespace ReductiveGroups.TorusUnipotent

open TauCeti WithConv Module CategoryTheory

attribute [local instance 100] LieRing.ofAssociativeRing

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "M" => Multiplicative (ι →₀ ℤ)
local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)

/-- **Lie triangularization of the Borel tangent** in an arbitrary
coordinate representation. -/
theorem BorelTorusUnipotentFlag.exists_upperTriangular_basis
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B) :
    ∃ b : Basis (Fin n) K (Fin n → K), ∀ d ∈ (derivationCompLieHom (B := K)
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range,
      matrixUpperGap 0 (matrixBasisConj b (affineGroupMatrixDifferential n ρ d)) := by
  let S := (derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
  let _ : LieAlgebra.IsSolvable S := borel_tangentImage_isSolvable J hJ
  let fS : S →ₗ⁅K⁆ Module.End K (Fin n → K) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
      Module.End K (Fin n → K)).toAlgHom.toLieHom.comp
      ((affineGroupMatrixDifferential n ρ).comp S.incl)
  let _ : LieRingModule S (Fin n → K) :=
    LieRingModule.compLieHom (Fin n → K) fS
  let _ : LieModule K S (Fin n → K) :=
    LieModule.compLieHom (Fin n → K) fS
  have hact (z : S) (v : Fin n → K) :
      ⁅z, v⁆ = Matrix.toLin' (affineGroupMatrixDifferential n ρ (z : _)) v := by
    rfl
  obtain ⟨b, hb⟩ := SolvableLieTriangularBasis.exists_upperTriangular_matrix_basis K S n
  refine ⟨b, fun d hd i j hij => ?_⟩
  let z : S := ⟨d, hd⟩
  rw [matrixBasisConj_apply, LinearMap.toMatrix_apply]
  change b.repr (Matrix.toLin' (affineGroupMatrixDifferential n ρ (z : _)) (b j)) i = 0
  rw [← hact z]
  exact hb z i j (by simpa using hij)

omit [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B] in
/-- The original torus tangent image lies in the original Borel tangent image. -/
theorem torusTangentImage_le_borelTangentImage
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (π : B →ₐc[K] MonoidAlgebra K M)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal) :
    diagonalizableTangentImage π ≤ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range := by
  intro d hd
  apply (tangent_mem_hopfQuotient_iff J d).mpr
  intro a ha
  obtain ⟨t, rfl⟩ := hd
  change t (π a) = 0
  rw [(hker a).mpr (hJI ha), map_zero]

omit [IsAlgClosed K] [Algebra.FiniteType K B] in
/-- Original torus points are upper triangular in a triangular basis
of the Borel tangent. -/
theorem torusPoint_pointBasisMatrix_upper
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (π : B →ₐc[K] MonoidAlgebra K M)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (b : Basis (Fin n) K (Fin n → K))
    (hb : ∀ d ∈ (derivationCompLieHom (B := K)
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range,
      matrixUpperGap 0 (matrixBasisConj b (affineGroupMatrixDifferential n ρ d)))
    (t : WithConv (MonoidAlgebra K M →ₐ[K] K)) :
    matrixUpperGap 0 (pointBasisMatrix n ρ b (AlgHom.mapDomain π t)) := by
  have htri : ∀ h : Derivation K (MonoidAlgebra K M)
      (Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K),
      matrixUpperGap 0 (LinearMap.toMatrix b b
        (Matrix.toLin' (affineGroupMatrixDifferential n (π.comp ρ) h))) := by
    intro h
    have hz : derivationComp (B := K) π h ∈ (derivationCompLieHom (B := K)
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range :=
      torusTangentImage_le_borelTangentImage I J hJI π hker
        (show derivationComp (B := K) π h ∈ diagonalizableTangentImage π from ⟨h, rfl⟩)
    have hcomp : affineGroupMatrixDifferential n (π.comp ρ) h =
        affineGroupMatrixDifferential n ρ (derivationComp (B := K) π h) := by
      rw [affineGroupMatrixDifferential_apply, affineGroupMatrixDifferential_apply]
      rw [derivationComp_comp, LinearMap.comp_apply]
    rw [hcomp]
    exact hb _ hz
  have hp := torusMatrixPoint_upper_of_tangents_upper (π.comp ρ) b htri t
  rw [AlgHom.mapDomain_comp] at hp
  exact hp

/-- Borel root Ga points are upper triangular in a triangular basis
of the Borel tangent. -/
theorem rootGaPoint_pointBasisMatrix_upper
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π)
    (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (b : Basis (Fin n) K (Fin n → K))
    (hb : ∀ d ∈ (derivationCompLieHom (B := K)
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range,
      matrixUpperGap 0 (matrixBasisConj b (affineGroupMatrixDifferential n ρ d)))
    (r : borelRootVectorIndex J π) (s : K) :
    matrixUpperGap 0 (pointBasisMatrix n ρ b
      (gaAffineGroupPoints (borelRootVectorGa J π hπ r) (Multiplicative.ofAdd s))) := by
  apply GaAffineGroupMatrixPoint.upper_of_tangent_upper
  rw [borelRootVectorGa_tangent]
  exact hb _ r.2.property.2.2

/-- Borel root Ga points lie in the original Ga-only subgroup `U`. -/
theorem rootGaPoint_mem_borelRootUnipotent
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) (r : borelRootVectorIndex J π) (s : K) :
    gaAffineGroupPoints (borelRootVectorGa J π hπ r) (Multiplicative.ofAdd s) ∈
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K) := by
  apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr
  intro a ha
  have hx : borelRootVectorGa J π hπ r a = 0 :=
    CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker
      (fun j => CommHopfAlgCat.ofHom (borelRootVectorGa J π hπ j)) r ha
  change ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd s)).ofConv (borelRootVectorGa J π hπ r a) = 0
  rw [hx, map_zero]

/-- Points of the Ga-only subgroup that are upper triangular in any basis
have unit diagonal there. -/
theorem BorelRootUnipotentPoint.pointBasisMatrix_diag
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (b : Basis (Fin n) K (Fin n → K)) (g : WithConv (B →ₐ[K] K))
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K))
    (hup : matrixUpperGap 0 (pointBasisMatrix n ρ b g)) (k : Fin n) :
    pointBasisMatrix n ρ b g k k = 1 := by
  have hpow := BorelRootUnipotentPoint.matrix_pow_sub_one_eq_zero J hJ π hπ n ρ g hg
  rw [← pointBasisMatrix_sub_one_pow_eq_zero_iff n ρ b g n] at hpow
  exact TorusUnipotent.UpperMatrix.diag_eq_one_of_sub_one_pow_eq_zero hup hpow k

omit [Algebra.FiniteType K B] in
/-- The diagonal entries of the torus points, in a triangular basis
of the Borel tangent, are characters of the split torus. -/
theorem BorelTorusUnipotentFlag.exists_pointBasisMatrix_diag_characters
    [Finite ι]
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (π : B →ₐc[K] MonoidAlgebra K M)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (b : Basis (Fin n) K (Fin n → K))
    (hb : ∀ d ∈ (derivationCompLieHom (B := K)
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range,
      matrixUpperGap 0 (matrixBasisConj b (affineGroupMatrixDifferential n ρ d))) :
    ∃ χ : Fin n → M, ∀ (t : WithConv (MonoidAlgebra K M →ₐ[K] K)) (k : Fin n),
      pointBasisMatrix n ρ b (AlgHom.mapDomain π t) k k =
        t.ofConv (MonoidAlgebra.single (χ k) 1) := by
  have hup := torusPoint_pointBasisMatrix_upper I J hJI π hker n ρ b hb
  have hk : ∀ k : Fin n, ∃ χ : M, ∀ t : WithConv (MonoidAlgebra K M →ₐ[K] K),
      pointBasisMatrix n ρ b (AlgHom.mapDomain π t) k k =
        t.ofConv (MonoidAlgebra.single χ 1) := by
    intro k
    let F : MonoidAlgebra K M := π (pointBasisEntry n ρ b k k)
    have hF (t : WithConv (MonoidAlgebra K M →ₐ[K] K)) :
        t.ofConv F = pointBasisMatrix n ρ b (AlgHom.mapDomain π t) k k := by
      rw [← pointBasisEntry_apply]
      rfl
    have hmul : ∀ s t : WithConv (MonoidAlgebra K M →ₐ[K] K),
        (s * t).ofConv F = s.ofConv F * t.ofConv F := by
      intro s t
      rw [hF, hF, hF, map_mul, pointBasisMatrix_mul]
      exact upperMatrix_mul_diag (hup s) (hup t) k
    have hF0 : F ≠ 0 := by
      intro h0
      have h1 := hF 1
      rw [h0, map_zero, map_one, pointBasisMatrix_one, Matrix.one_apply_eq] at h1
      exact zero_ne_one h1
    obtain ⟨χ, hχ⟩ :=
      TorusUnipotent.BorelTorusUnipotentCharacters.exists_of_torusPoint_multiplicative F hF0 hmul
    exact ⟨χ, fun t => (hF t).symm.trans (hχ t)⟩
  choose χ hχ using hk
  exact ⟨χ, fun t k => hχ k t⟩

end TorusUnipotent
