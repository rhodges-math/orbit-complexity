import OrbitComplexity.GroupActions.Varieties.BorelVariety
import OrbitComplexity.GroupActions.Varieties.AffineGroup

/-! # Rational points of Borel varieties

The rational points of the chosen Borel variety identify with the subgroup of reductive
group points annihilating its defining Hopf ideal.

## Main definitions

* `GroupActions.borelPointsMulEquiv`: the rational-point subgroup identification.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem borelPointsReduced : IsReduced G.borelAlgebra := by
  have : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  exact TauCeti.isReduced_of_smooth K G.borelAlgebra

attribute [local instance] borelPointsReduced

set_option backward.isDefEq.respectTransparency.types false in
/-- Rational points of the Borel variety are the chosen subgroup of reductive group points. -/
def borelPointsMulEquiv : (borelVariety G).points ≃* G.borelPoints :=
  (affineGroupPointsMulEquiv K G.borelAlgebra).symm.trans
    (MonoidHom.ofInjective
      (f := (TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.borelIdeal (CommAlgCat.of K K)).hom)
      (TauCeti.CommHopfAlgCat.quotientPointsHom_injective _ _ _))

/-- The Borel-point identification includes a quotient coordinate point into ambient points. -/
theorem borelPointsMulEquiv_coe (x : (borelVariety G).points) :
    (borelPointsMulEquiv G x : G.points) =
      TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.borelIdeal (CommAlgCat.of K K)
        (WithConv.toConv (affinePointsEquiv.symm x)) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The point-subgroup identification commutes with the inclusion of Borel varieties. -/
theorem borelInclusion_points (x : (borelVariety G).points) :
    Variety.mapPoints (borelInclusion G) x =
      reductivePointsEquiv G (borelPointsMulEquiv G x) := by
  let e : (G.borelAlgebra →ₐ[K] K) ≃ (borelVariety G).points := affinePointsEquiv
  obtain ⟨f, rfl⟩ := e.surjective x
  have hf : (borelPointsMulEquiv G (e f) : G.points) =
      TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.borelIdeal (CommAlgCat.of K K)
        (WithConv.toConv f) := by
    rw [borelPointsMulEquiv_coe]
    change TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.borelIdeal (CommAlgCat.of K K)
        (WithConv.toConv (e.symm (e f))) = _
    rw [e.symm_apply_apply]
  apply Subtype.ext
  change (e f).val ≫ (borelInclusion G).left =
    (reductivePointsEquiv G (borelPointsMulEquiv G (e f) : G.points)).val
  rw [hf, reductivePointsEquiv_apply, borelInclusion_left]
  change AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk G.borelIdeal.toIdeal)) =
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (f.comp (Ideal.Quotient.mkₐ K G.borelIdeal.toIdeal)).toRingHom)
  rw [← AlgebraicGeometry.Spec.map_comp]
  rfl

end

end GroupActions
