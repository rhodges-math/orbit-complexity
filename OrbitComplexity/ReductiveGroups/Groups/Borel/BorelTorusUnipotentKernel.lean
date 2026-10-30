import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTorusUnipotentFlag
import OrbitComplexity.ReductiveGroups.Groups.Unipotent.BorelRootUnipotentLieDecomposition
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaMatrixLogarithm
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaUnitPointSubgroupCriterion
import OrbitComplexity.ReductiveGroups.Groups.Generated.GaGeneratedTangentCriterion

/-!
# Borel Torus Unipotent Kernel

**Unipotent points of the Borel lie in its Ga-only subgroup.**

Let `g` be a `K`-point of the Borel whose matrix in a faithful
coordinate representation `ρ` is unipotent. The Ga curve through `g`
(`ReductiveGroups.UnipotentPointGaIntegration.existsUnique_of_matrix_point_unipotent`) factors
through the
Borel, since its parameter-one point does; so its tangent `d` lies in the
Borel tangent, which is the torus tangent plus the tangent
of the Ga-only subgroup `U` (Cartan weight decomposition and
`ReductiveGroups.BorelRootUnipotentTangent.eq_character_sum`). In a triangular basis for the
Borel tangent the represented `d` is the finite logarithm of the unipotent
upper triangular matrix of `g`, hence strictly upper triangular; the `U`-part
is nilpotent and upper triangular, hence strictly upper triangular. So the
torus part is represented nilpotently and vanishes by faithfulness. Thus
`d ∈ Lie(U)`, the whole Ga curve factors through `U`, and `g ∈ U(K)`. -/

noncomputable section
namespace ReductiveGroups.TorusUnipotent

open TauCeti WithConv Module LieAlgebra LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "M" => Multiplicative (ι →₀ ℤ)
local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)

/-- The Borel tangent is the sum of the torus tangent and
the tangent of the Ga-only Borel subgroup. -/
theorem BorelTangent.le_torus_sup_borelRootUnipotentTangent
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range.toSubmodule ≤
      (diagonalizableTangentImage π).toSubmodule ⊔
        (derivationCompLieHom (B := K)
          (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
            (borelRootUnipotentHopfIdeal J π hπ)).hom).range.toSubmodule := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let S := (derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
  let N : Submodule K 𝔤 := ⨆ (α : M) (_ : α ≠ 1),
    S.toSubmodule ⊓ affineGroupCharacterWeightSpace π α
  have hHS : H ≤ S := torusTangentImage_le_borelTangentImage I J hJI π hker
  have hNU := BorelRootUnipotentTangent.eq_character_sum I J hJI hI hJ π hπ hker hB
  change S.toSubmodule ≤ H.toSubmodule ⊔ _
  rw [hNU]
  change (cartanStableSubmodule H S hHS).toSubmodule ≤ H.toSubmodule ⊔ N
  rw [CartanStableSubmodule.eq_iSup_inf_rootSpace H S hHS]
  simp only [LieSubmodule.iSup_toSubmodule]
  refine iSup_le fun χ => ?_
  intro d hd
  have hdS : d ∈ S := hd.1
  have hdroot : d ∈ rootSpace H χ := hd.2
  by_cases hχ : χ.IsZero
  · have hz : rootSpace H χ = H.toLieSubmodule := by
      simpa only [hχ.eq] using (rootSpace_zero_eq K 𝔤 H)
    rw [hz] at hdroot
    exact (le_sup_left : H.toSubmodule ≤ H.toSubmodule ⊔ N) hdroot
  · obtain ⟨α, ⟨_, hαχ⟩, _⟩ := existsUnique_character_of_lieWeight π hπ χ
    have hα : α ≠ 1 := by
      intro ha
      apply hχ
      change (χ : H → K) = 0
      rw [hαχ, ha, characterDifferentialOnImage_one]
      rfl
    have hdW : d ∈ affineGroupCharacterWeightSpace π α := by
      rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ α]
      change d ∈ rootSpace H (characterDifferentialOnImage π hπ α)
      exact hαχ ▸ hdroot
    have hdN : d ∈ N :=
      (le_iSup₂_of_le α hα le_rfl :
        S.toSubmodule ⊓ affineGroupCharacterWeightSpace π α ≤ N) ⟨hdS, hdW⟩
    exact (le_sup_right : N ≤ H.toSubmodule ⊔ N) hdN

/-- **Unipotent Borel points lie in `U`.** A `K`-point of the Borel
that is represented by a unipotent matrix in some faithful coordinate
representation is a `K`-point of the original Ga-only Borel subgroup. -/
theorem BorelPoint.borelRootUnipotent_of_matrix_unipotent
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (g : WithConv (B →ₐ[K] K))
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) J
      (CommAlgCat.of K K))
    (hu : IsNilpotent ((GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g) :
      Matrix (Fin n) (Fin n) K) - 1)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K) := by
  obtain ⟨b, hb⟩ := TorusUnipotent.BorelTorusUnipotentFlag.exists_upperTriangular_basis J hJ n ρ
  obtain ⟨χ, hχ⟩ :=
    TorusUnipotent.BorelTorusUnipotentFlag.exists_pointBasisMatrix_diag_characters I J hJI π hker n
      ρ b hb
  have hup : matrixUpperGap 0 (pointBasisMatrix n ρ b g) :=
    (borelPoint_upper_and_diagonal_relations I J hJI hI hJ π hπ hker hB n ρ b hb χ hχ
      g hg).1
  obtain ⟨r, hr⟩ := hu
  have hr' : (pointBasisMatrix n ρ b g - 1) ^ r = 0 :=
    (pointBasisMatrix_sub_one_pow_eq_zero_iff n ρ b g r).mpr hr
  have hdiag : ∀ k, pointBasisMatrix n ρ b g k k = 1 :=
    TorusUnipotent.UpperMatrix.diag_eq_one_of_sub_one_pow_eq_zero hup hr'
  -- The Ga curve through `g`, inside the Borel.
  obtain ⟨x, hx, -⟩ := UnipotentPointGaIntegration.existsUnique_of_matrix_point_unipotent n ρ hρ g
    ⟨r, hr⟩
  have hxJ : ∀ a ∈ J, x a = 0 :=
    (GaMorphism.kills_hopfIdeal_iff_unitPoint_mem x J).mpr (by rw [hx]; exact hg)
  have hdS : gaAffineGroupTangent x ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range :=
    (tangent_mem_hopfQuotient_iff J _).mpr ((gaMorphism_kills_hopfIdeal_iff x J).mp hxJ)
  -- Its represented tangent is strictly upper triangular in the basis `b`.
  have hpow : ((GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ
      (gaAffineGroupPoints x (Multiplicative.ofAdd 1))) :
        Matrix (Fin n) (Fin n) K) - 1) ^ (r + 1) = 0 := by
    rw [hx, pow_succ, hr, zero_mul]
  have hlog := GaAffineGroupTangent.matrix_eq_finite_logarithm n x ρ r hpow
  have hdgap : matrixUpperGap 1
      (matrixBasisConj b (affineGroupMatrixDifferential n ρ (gaAffineGroupTangent x))) := by
    rw [hlog, hx, map_sum]
    simp only [map_smul, map_pow, map_sub, map_one]
    exact matrixUpperGap_one_finite_logarithm hup hdiag r _
  -- Decompose the tangent into its torus and `U` parts.
  obtain ⟨dT, hdT, dU, hdU, hsum⟩ := Submodule.mem_sup.mp
    (TorusUnipotent.BorelTangent.le_torus_sup_borelRootUnipotentTangent I J hJI hI hJ π hπ hker hB
      hdS)
  have hdUS : dU ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range :=
    hopfQuotient_tangentImage_antitone (borelRootUnipotentHopfIdeal J π hπ) J
      (borel_le_borelRootUnipotentHopfIdeal J π hπ) hdU
  have hUdiag : ∀ k,
      matrixBasisConj b (affineGroupMatrixDifferential n ρ dU) k k = 0 := by
    apply upperMatrix_diag_eq_zero_of_pow_eq_zero (hb dU hdUS) (m := n)
    exact (matrixBasisConj_pow_eq_zero_iff b _ n).mpr
      (BorelRootUnipotentTangent.matrix_pow_eq_zero J hJ π hπ n ρ dU hdU)
  have hTS := torusTangentImage_le_borelTangentImage I J hJI π hker hdT
  have hTeq : matrixBasisConj b (affineGroupMatrixDifferential n ρ dT) =
      matrixBasisConj b (affineGroupMatrixDifferential n ρ (gaAffineGroupTangent x)) -
        matrixBasisConj b (affineGroupMatrixDifferential n ρ dU) := by
    rw [← hsum, map_add, map_add]
    abel
  have hTgap : matrixUpperGap 1
      (matrixBasisConj b (affineGroupMatrixDifferential n ρ dT)) := by
    apply matrixUpperGap_one_of_diag_eq_zero (hb dT hTS)
    intro k
    rw [hTeq, Matrix.sub_apply, hdgap k k (by omega), hUdiag k, sub_zero]
  have hTnil : IsNilpotent (affineGroupMatrixDifferential n ρ dT) :=
    ⟨n, (matrixBasisConj_pow_eq_zero_iff b _ n).mp
      (pow_card_eq_zero_of_matrixUpperGap_one hTgap)⟩
  have hT0 : dT = 0 :=
    TorusTangent.eq_zero_of_faithful_matrix_nilpotent π n ρ hρ dT hdT hTnil
  have hdU' : gaAffineGroupTangent x ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range := by
    rw [← hsum, hT0, zero_add]
    exact hdU
  -- The whole Ga curve lies in `U`, hence so does its parameter-one point.
  have hxU : ∀ a ∈ borelRootUnipotentHopfIdeal J π hπ, x a = 0 :=
    (gaMorphism_kills_hopfIdeal_iff x _).mpr ((tangent_mem_hopfQuotient_iff _ _).mp hdU')
  have h1 := (GaMorphism.kills_hopfIdeal_iff_unitPoint_mem x _).mp hxU
  rwa [hx] at h1

end TorusUnipotent
