import OrbitComplexity.GroupActions.Varieties.RootSubgroupVariety
import OrbitComplexity.GroupActions.Varieties.AffineGroup

/-! # Rational points of closed root subgroups

The affine root variety has exactly the specified subgroup of reductive group points.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)
  (R : Set G.rootIndex) (hR : ReductiveGroups.IsPositiveRootClosed G.rootBase R)

/-- Rational points of a root variety identify with its root-support subgroup. -/
def rootSubsetPointsMulEquiv :
    (rootSubsetVariety G R hR).points ≃* G.rootSubsetPoints R hR :=
  (affineGroupPointsMulEquiv K (G.rootSubsetAlgebra R hR)).symm.trans
    (MonoidHom.ofInjective
      (f := (TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) (G.rootSubsetIdeal R hR)
        (CommAlgCat.of K K)).hom)
      (TauCeti.CommHopfAlgCat.quotientPointsHom_injective _ _ _))

private theorem rootSubsetPoints_coe (x : (rootSubsetVariety G R hR).points) :
    (rootSubsetPointsMulEquiv G R hR x : G.points) =
      TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) (G.rootSubsetIdeal R hR)
        (CommAlgCat.of K K) (WithConv.toConv (affinePointsEquiv.symm x)) := rfl

/-- The root-subgroup point identification commutes with its inclusion into group points. -/
theorem rootSubsetInclusion_points (x : (rootSubsetVariety G R hR).points) :
    Variety.mapPoints (rootSubsetInclusion G R hR) x =
      reductivePointsEquiv G (rootSubsetPointsMulEquiv G R hR x) := by
  let e : (G.rootSubsetAlgebra R hR →ₐ[K] K) ≃ (rootSubsetVariety G R hR).points :=
    affinePointsEquiv
  obtain ⟨f, rfl⟩ := e.surjective x
  have hf : (rootSubsetPointsMulEquiv G R hR (e f) : G.points) =
      TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) (G.rootSubsetIdeal R hR)
        (CommAlgCat.of K K) (WithConv.toConv f) := by
    rw [rootSubsetPoints_coe]
    change TauCeti.CommHopfAlgCat.quotientPointsHom
      (CommHopfAlgCat.of K G.coordinateAlgebra) (G.rootSubsetIdeal R hR) (CommAlgCat.of K K)
      (WithConv.toConv (e.symm (e f))) = _
    rw [e.symm_apply_apply]
  apply Subtype.ext
  change (e f).val ≫ (rootSubsetInclusion G R hR).left =
    (reductivePointsEquiv G (rootSubsetPointsMulEquiv G R hR (e f) : G.points)).val
  rw [hf, reductivePointsEquiv_apply, rootSubsetInclusion_left]
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (G.rootSubsetIdeal R hR).toIdeal)) =
    Spec.map (CommRingCat.ofHom
      (f.comp (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal R hR).toIdeal)).toRingHom)
  rw [← Spec.map_comp]
  rfl

end
end GroupActions
