import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBruhatSystem
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaTangentDeterminesMorphism
import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Tangent

/-! # Additive root parameters with prescribed tangent -/

noncomputable section

namespace ReductiveGroups

open TauCeti

universe u
variable {K : Type u} [Field K]

private def gaScalarMap (c : K) : SymmetricAlgebra K K →ₐc[K] SymmetricAlgebra K K :=
  BialgHom.ofAlgHom
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι K K).comp (c • LinearMap.id)))
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro a
      simp [SymmetricAlgebra.algebraMapInv_ι])
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro a
      simp [SymmetricAlgebra.comul_ι])

private theorem gaScalarMap_ι (c a : K) :
    gaScalarMap c (SymmetricAlgebra.ι K K a) = SymmetricAlgebra.ι K K (c * a) := by
  simp [gaScalarMap]

private theorem origin_scalar (c : K) :
    derivationComp (B := K) (gaScalarMap c) (gaOriginDerivation K) =
      c • gaOriginDerivation K := by
  apply (AdditiveGroup.gaTangentLinearEquiv (R := K) (B := K)).injective
  rw [AdditiveGroup.gaTangentLinearEquiv_apply, algEquivSelf_derivationComp_apply]
  change Bialgebra.CounitAlgebra.algEquivSelf K (SymmetricAlgebra K K) K
    (gaOriginDerivation K (gaScalarMap c (SymmetricAlgebra.ι K K 1))) = _
  have h : SymmetricAlgebra.ι K K c = c • SymmetricAlgebra.ι K K 1 := by
    rw [← map_smul]
    simp
  have hval : Bialgebra.CounitAlgebra.algEquivSelf K (SymmetricAlgebra K K) K
      (gaOriginDerivation K (SymmetricAlgebra.ι K K c)) = c := by
    calc
      _ = c • Bialgebra.CounitAlgebra.algEquivSelf K (SymmetricAlgebra K K) K
          (gaOriginDerivation K (SymmetricAlgebra.ι K K 1)) := by
        rw [h, Derivation.map_smul]
        exact (Bialgebra.CounitAlgebra.algEquivSelf K
          (SymmetricAlgebra K K) K).toLinearMap.map_smul c _
      _ = c := by rw [gaOriginDerivation_generator, smul_eq_mul, mul_one]
  rw [gaScalarMap_ι, mul_one, hval]
  simp only [map_smul, AdditiveGroup.gaTangentLinearEquiv_apply,
    gaOriginDerivation_generator, smul_eq_mul, mul_one]

private theorem gaScalar_tangent {B : Type u} [CommRing B] [HopfAlgebra K B]
    (x : B →ₐc[K] SymmetricAlgebra K K) (c : K) :
    gaAffineGroupTangent ((gaScalarMap c).comp x) = c • gaAffineGroupTangent x := by
  unfold gaAffineGroupTangent
  rw [derivationComp_comp, LinearMap.comp_apply, origin_scalar, map_smul]

namespace ReductiveGroupData

variable [CharZero K] [IsAlgClosed K] (G : ReductiveGroupData K)

/-- Every vector in a root-character tangent space integrates uniquely to an additive parameter. -/
theorem existsUnique_rootParameter (r : G.rootIndex) (d : G.tangent)
    (hd : d ∈ G.rootWeightSpace r) :
    ∃! φ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K, gaAffineGroupTangent φ = d := by
  let alpha := G.characterRootEquiv.symm r
  let x := (characterSl2PairChoice G.torusIdeal G.isMaximalTorus G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive alpha).1
  have hx := characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive alpha
  have hm : gaAffineGroupTangent x ∈ G.rootWeightSpace r := hx.tangent_mem
  have hn : (⟨gaAffineGroupTangent x, hm⟩ : G.rootWeightSpace r) ≠ 0 := by
    intro h
    exact hx.tangent_ne_zero (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hn).mp
    (G.rootWeightSpace_finrank r) (⟨d, hd⟩ : G.rootWeightSpace r)
  have he : gaAffineGroupTangent ((gaScalarMap c).comp x) = d := by
    rw [gaScalar_tangent]
    exact congrArg Subtype.val hc
  refine ⟨(gaScalarMap c).comp x, he, ?_⟩
  intro y hy
  exact gaMorphism_ext_of_tangent_eq y _ (hy.trans he.symm)

end ReductiveGroupData

end ReductiveGroups
