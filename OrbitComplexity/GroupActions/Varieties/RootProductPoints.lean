import OrbitComplexity.GroupActions.Varieties.RootSubgroupProduct

/-! # Rational multiplication in root-product charts

The root-product isomorphism multiplies its two subgroup coordinates on rational points.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GroupActions
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)
  (R R₁ R₂ : Set G.rootIndex)
  (hR : ReductiveGroups.IsPositiveRootClosed G.rootBase R)
  (hR₁ : ReductiveGroups.IsPositiveRootClosed G.rootBase R₁)
  (hR₂ : ReductiveGroups.IsPositiveRootClosed G.rootBase R₂)

/-- The root-product isomorphism acts on rational points by multiplying its two factors. -/
theorem rootProductIso_points (hunion : R = R₁ ∪ R₂) (hdisj : Disjoint R₁ R₂)
    (x : (rootProductVariety G R₁ R₂ hR₁ hR₂).points) :
    Variety.mapPoints ((rootProductIso G R R₁ R₂ hR hR₁ hR₂ hunion hdisj).hom ≫
      rootSubsetInclusion G R hR) x =
      reductivePointsEquiv G
        ((rootSubsetPointsMulEquiv G R₁ hR₁ (rootProductPointsEquiv G R₁ R₂ hR₁ hR₂ x).1 :
          G.points) *
          (rootSubsetPointsMulEquiv G R₂ hR₂ (rootProductPointsEquiv G R₁ R₂ hR₁ hR₂ x).2 :
            G.points)) := by
  rw [rootProductIso_hom_comp]
  let e : (G.rootSubsetAlgebra R₁ hR₁ ⊗[K] G.rootSubsetAlgebra R₂ hR₂ →ₐ[K] K) ≃
      (rootProductVariety G R₁ R₂ hR₁ hR₂).points := affinePointsEquiv
  obtain ⟨q, rfl⟩ := e.surjective x
  let p := tensorAlgebraPointsEquiv K (G.rootSubsetAlgebra R₁ hR₁)
    (G.rootSubsetAlgebra R₂ hR₂) q
  let eA : (G.rootSubsetAlgebra R₁ hR₁ →ₐ[K] K) ≃
      (rootSubsetVariety G R₁ hR₁).points := affinePointsEquiv
  let eB : (G.rootSubsetAlgebra R₂ hR₂ →ₐ[K] K) ≃
      (rootSubsetVariety G R₂ hR₂).points := affinePointsEquiv
  let q₁ := Ideal.Quotient.mkₐ K (G.rootSubsetIdeal R₁ hR₁).toIdeal
  let q₂ := Ideal.Quotient.mkₐ K (G.rootSubsetIdeal R₂ hR₂).toIdeal
  have hpair : rootProductPointsEquiv G R₁ R₂ hR₁ hR₂ (e q) = (eA p.1, eB p.2) := by
    change affineProductPointsEquiv K (G.rootSubsetAlgebra R₁ hR₁)
      (G.rootSubsetAlgebra R₂ hR₂) (affinePointsEquiv q) = _
    simp only [affineProductPointsEquiv, Equiv.trans_apply,
      Equiv.symm_apply_apply, Equiv.prodCongr_apply]
    rfl
  have hA : (rootSubsetPointsMulEquiv G R₁ hR₁ (eA p.1) : G.points) =
      WithConv.toConv (p.1.comp q₁) := by
    change TauCeti.CommHopfAlgCat.quotientPointsHom
      (CommHopfAlgCat.of K G.coordinateAlgebra) (G.rootSubsetIdeal R₁ hR₁)
      (CommAlgCat.of K K) (WithConv.toConv (eA.symm (eA p.1))) = _
    rw [eA.symm_apply_apply]
    rfl
  have hB : (rootSubsetPointsMulEquiv G R₂ hR₂ (eB p.2) : G.points) =
      WithConv.toConv (p.2.comp q₂) := by
    change TauCeti.CommHopfAlgCat.quotientPointsHom
      (CommHopfAlgCat.of K G.coordinateAlgebra) (G.rootSubsetIdeal R₂ hR₂)
      (CommAlgCat.of K K) (WithConv.toConv (eB.symm (eB p.2))) = _
    rw [eB.symm_apply_apply]
    rfl
  rw [hpair, hA, hB]
  apply Subtype.ext
  rw [reductivePointsEquiv_apply]
  change Spec.map (CommRingCat.ofHom q.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (affineMulMap q₁ q₂).toRingHom) =
    Spec.map (CommRingCat.ofHom
      ((WithConv.toConv (p.1.comp q₁) * WithConv.toConv (p.2.comp q₂)).ofConv).toRingHom)
  rw [← Spec.map_comp]
  have hq := affineMulMap_points q₁ q₂ p
  change ((tensorAlgebraPointsEquiv K (G.rootSubsetAlgebra R₁ hR₁)
    (G.rootSubsetAlgebra R₂ hR₂)).symm
      ((tensorAlgebraPointsEquiv K (G.rootSubsetAlgebra R₁ hR₁)
        (G.rootSubsetAlgebra R₂ hR₂)) q)).comp (affineMulMap q₁ q₂) = _ at hq
  rw [Equiv.symm_apply_apply] at hq
  exact congrArg (fun φ : G.coordinateAlgebra →ₐ[K] K =>
    Spec.map (CommRingCat.ofHom φ.toRingHom)) hq

end
end GroupActions
