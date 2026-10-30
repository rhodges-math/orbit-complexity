import OrbitComplexity.GroupActions.Varieties.TorusVariety
import OrbitComplexity.GroupActions.Varieties.AffineGroup

/-! # Rational points of torus varieties

The rational points of the chosen torus variety identify with the subgroup of reductive
group points annihilating its defining Hopf ideal.

## Main definitions

* `GroupActions.torusPointsMulEquiv`: the rational-point subgroup identification.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem torusPointsReduced : IsReduced G.torusAlgebra := by
  have : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra

attribute [local instance] torusPointsReduced

set_option backward.isDefEq.respectTransparency.types false in
/-- Rational points of the torus variety are the chosen subgroup of reductive group points. -/
def torusPointsMulEquiv : (torusVariety G).points ≃* G.torusPoints :=
  (affineGroupPointsMulEquiv K G.torusAlgebra).symm.trans
    (MonoidHom.ofInjective
      (f := (TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.torusIdeal (CommAlgCat.of K K)).hom)
      (TauCeti.CommHopfAlgCat.quotientPointsHom_injective _ _ _))

/-- The torus-point identification includes a quotient coordinate point into ambient points. -/
theorem torusPointsMulEquiv_coe (x : (torusVariety G).points) :
    (torusPointsMulEquiv G x : G.points) =
      TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.torusIdeal (CommAlgCat.of K K)
        (WithConv.toConv (affinePointsEquiv.symm x)) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The point-subgroup identification commutes with the inclusion of torus varieties. -/
theorem torusInclusion_points (x : (torusVariety G).points) :
    Variety.mapPoints (torusInclusion G) x =
      reductivePointsEquiv G (torusPointsMulEquiv G x) := by
  let e : (G.torusAlgebra →ₐ[K] K) ≃ (torusVariety G).points := affinePointsEquiv
  obtain ⟨f, rfl⟩ := e.surjective x
  have hf : (torusPointsMulEquiv G (e f) : G.points) =
      TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.torusIdeal (CommAlgCat.of K K)
        (WithConv.toConv f) := by
    rw [torusPointsMulEquiv_coe]
    change TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.torusIdeal (CommAlgCat.of K K)
        (WithConv.toConv (e.symm (e f))) = _
    rw [e.symm_apply_apply]
  apply Subtype.ext
  change (e f).val ≫ (torusInclusion G).left =
    (reductivePointsEquiv G (torusPointsMulEquiv G (e f) : G.points)).val
  rw [hf, reductivePointsEquiv_apply, torusInclusion_left]
  change AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk G.torusIdeal.toIdeal)) =
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (f.comp (Ideal.Quotient.mkₐ K G.torusIdeal.toIdeal)).toRingHom)
  rw [← AlgebraicGeometry.Spec.map_comp]
  rfl

end

end GroupActions
