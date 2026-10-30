import OrbitComplexity.GroupActions.Varieties.UnipotentVariety
import OrbitComplexity.GroupActions.Varieties.AffineGroup

/-! # Rational points of Unipotent varieties

The rational points of the chosen unipotent variety identify with the subgroup of reductive
group points annihilating its defining Hopf ideal.

## Main definitions

* `GroupActions.unipotentPointsMulEquiv`: the rational-point subgroup identification.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem unipotentPointsReduced : IsReduced G.unipotentAlgebra := by
  have : Algebra.Smooth K G.unipotentAlgebra := G.unipotent_smooth
  exact TauCeti.isReduced_of_smooth K G.unipotentAlgebra

attribute [local instance] unipotentPointsReduced

set_option backward.isDefEq.respectTransparency.types false in
/-- Rational points of the Unipotent variety are the chosen subgroup of reductive group points. -/
def unipotentPointsMulEquiv : (unipotentVariety G).points ≃* G.unipotentPoints :=
  (affineGroupPointsMulEquiv K G.unipotentAlgebra).symm.trans
    (MonoidHom.ofInjective
      (f := (TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.unipotentIdeal (CommAlgCat.of K K)).hom)
      (TauCeti.CommHopfAlgCat.quotientPointsHom_injective _ _ _))

/-- The unipotent-point identification includes a quotient coordinate point into ambient points. -/
theorem unipotentPointsMulEquiv_coe (x : (unipotentVariety G).points) :
    (unipotentPointsMulEquiv G x : G.points) =
      TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.unipotentIdeal (CommAlgCat.of K K)
        (WithConv.toConv (affinePointsEquiv.symm x)) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The point-subgroup identification commutes with the inclusion of Unipotent varieties. -/
theorem unipotentInclusion_points (x : (unipotentVariety G).points) :
    Variety.mapPoints (unipotentInclusion G) x =
      reductivePointsEquiv G (unipotentPointsMulEquiv G x) := by
  let e : (G.unipotentAlgebra →ₐ[K] K) ≃ (unipotentVariety G).points := affinePointsEquiv
  obtain ⟨f, rfl⟩ := e.surjective x
  have hf : (unipotentPointsMulEquiv G (e f) : G.points) =
      TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.unipotentIdeal (CommAlgCat.of K K)
        (WithConv.toConv f) := by
    rw [unipotentPointsMulEquiv_coe]
    change TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.unipotentIdeal (CommAlgCat.of K K)
        (WithConv.toConv (e.symm (e f))) = _
    rw [e.symm_apply_apply]
  apply Subtype.ext
  change (e f).val ≫ (unipotentInclusion G).left =
    (reductivePointsEquiv G (unipotentPointsMulEquiv G (e f) : G.points)).val
  rw [hf, reductivePointsEquiv_apply, unipotentInclusion_left]
  change AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk G.unipotentIdeal.toIdeal)) =
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (f.comp (Ideal.Quotient.mkₐ K G.unipotentIdeal.toIdeal)).toRingHom)
  rw [← AlgebraicGeometry.Spec.map_comp]
  rfl

end

end GroupActions
