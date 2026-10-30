import OrbitComplexity.GroupActions.Varieties.OppositeUnipotentVariety
import OrbitComplexity.GroupActions.Varieties.AffineGroup
import OrbitComplexity.GroupActions.Varieties.OpenPoints

/-! # Rational points of opposite unipotent varieties

The rational points of the opposite unipotent variety identify with the subgroup of reductive
group points annihilating its defining Hopf ideal.

## Main definitions

* `GroupActions.oppositeUnipotentPointsMulEquiv`: the rational-point subgroup identification.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem oppositeUnipotentPointsReduced : IsReduced G.oppositeUnipotentAlgebra := by
  have : Algebra.Smooth K G.oppositeUnipotentAlgebra := G.oppositeUnipotent_smooth
  exact TauCeti.isReduced_of_smooth K G.oppositeUnipotentAlgebra

attribute [local instance] oppositeUnipotentPointsReduced

set_option backward.isDefEq.respectTransparency.types false in
/-- Points of the opposite unipotent variety form its specified subgroup of group points. -/
def oppositeUnipotentPointsMulEquiv :
    (oppositeUnipotentVariety G).points ≃* G.oppositeUnipotentPoints :=
  (affineGroupPointsMulEquiv K G.oppositeUnipotentAlgebra).symm.trans
    (MonoidHom.ofInjective
      (f := (TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeUnipotentIdeal (CommAlgCat.of K K)).hom)
      (TauCeti.CommHopfAlgCat.quotientPointsHom_injective _ _ _))

/-- The opposite unipotent point identification includes quotient points into ambient points. -/
theorem oppositeUnipotentPointsMulEquiv_coe (x : (oppositeUnipotentVariety G).points) :
    (oppositeUnipotentPointsMulEquiv G x : G.points) =
      TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeUnipotentIdeal (CommAlgCat.of K K)
        (WithConv.toConv (affinePointsEquiv.symm x)) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The point subgroup identification commutes with the opposite unipotent inclusion. -/
theorem oppositeUnipotentInclusion_points (x : (oppositeUnipotentVariety G).points) :
    Variety.mapPoints (oppositeUnipotentInclusion G) x =
      reductivePointsEquiv G (oppositeUnipotentPointsMulEquiv G x) := by
  let e : (G.oppositeUnipotentAlgebra →ₐ[K] K) ≃ (oppositeUnipotentVariety G).points :=
    affinePointsEquiv
  obtain ⟨f, rfl⟩ := e.surjective x
  have hf : (oppositeUnipotentPointsMulEquiv G (e f) : G.points) =
      TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeUnipotentIdeal (CommAlgCat.of K K)
        (WithConv.toConv f) := by
    rw [oppositeUnipotentPointsMulEquiv_coe]
    change TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeUnipotentIdeal (CommAlgCat.of K K)
        (WithConv.toConv (e.symm (e f))) = _
    rw [e.symm_apply_apply]
  apply Subtype.ext
  change (e f).val ≫ (oppositeUnipotentInclusion G).left =
    (reductivePointsEquiv G (oppositeUnipotentPointsMulEquiv G (e f) : G.points)).val
  rw [hf, reductivePointsEquiv_apply, oppositeUnipotentInclusion_left]
  change AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk G.oppositeUnipotentIdeal.toIdeal)) =
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (f.comp (Ideal.Quotient.mkₐ K G.oppositeUnipotentIdeal.toIdeal)).toRingHom)
  rw [← AlgebraicGeometry.Spec.map_comp]
  rfl

end

end GroupActions
