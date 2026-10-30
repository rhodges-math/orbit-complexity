import OrbitComplexity.GroupActions.Varieties.OppositeBorelVariety
import OrbitComplexity.GroupActions.Varieties.AffineGroup

/-! # Rational points of opposite Borel varieties

The rational points of the opposite Borel variety identify with the subgroup of reductive
group points annihilating its defining Hopf ideal.

## Main definitions

* `GroupActions.oppositeBorelPointsMulEquiv`: the rational-point subgroup identification.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem oppositeBorelPointsReduced : IsReduced G.oppositeBorelAlgebra := by
  have : Algebra.Smooth K G.oppositeBorelAlgebra := G.oppositeBorel_smooth
  exact TauCeti.isReduced_of_smooth K G.oppositeBorelAlgebra

attribute [local instance] oppositeBorelPointsReduced

/-- Rational points of the opposite Borel variety identify with its subgroup of group points. -/
def oppositeBorelPointsMulEquiv : (oppositeBorelVariety G).points ≃* G.oppositeBorelPoints :=
  (affineGroupPointsMulEquiv K G.oppositeBorelAlgebra).symm.trans
    (MonoidHom.ofInjective
      (f := (TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeBorelIdeal (CommAlgCat.of K K)).hom)
      (TauCeti.CommHopfAlgCat.quotientPointsHom_injective _ _ _))

/-- The opposite Borel-point identification includes quotient points into ambient points. -/
theorem oppositeBorelPointsMulEquiv_coe (x : (oppositeBorelVariety G).points) :
    (oppositeBorelPointsMulEquiv G x : G.points) =
      TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeBorelIdeal (CommAlgCat.of K K)
        (WithConv.toConv (affinePointsEquiv.symm x)) := rfl

/-- The point-subgroup identification commutes with the inclusion of opposite Borel varieties. -/
theorem oppositeBorelInclusion_points (x : (oppositeBorelVariety G).points) :
    Variety.mapPoints (oppositeBorelInclusion G) x =
      reductivePointsEquiv G (oppositeBorelPointsMulEquiv G x) := by
  let e : (G.oppositeBorelAlgebra →ₐ[K] K) ≃ (oppositeBorelVariety G).points := affinePointsEquiv
  obtain ⟨f, rfl⟩ := e.surjective x
  have hf : (oppositeBorelPointsMulEquiv G (e f) : G.points) =
      TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeBorelIdeal (CommAlgCat.of K K)
        (WithConv.toConv f) := by
    rw [oppositeBorelPointsMulEquiv_coe]
    change TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeBorelIdeal (CommAlgCat.of K K)
        (WithConv.toConv (e.symm (e f))) = _
    rw [e.symm_apply_apply]
  apply Subtype.ext
  change (e f).val ≫ (oppositeBorelInclusion G).left =
    (reductivePointsEquiv G (oppositeBorelPointsMulEquiv G (e f) : G.points)).val
  rw [hf, reductivePointsEquiv_apply, oppositeBorelInclusion_left]
  change AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk G.oppositeBorelIdeal.toIdeal)) =
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (f.comp (Ideal.Quotient.mkₐ K G.oppositeBorelIdeal.toIdeal)).toRingHom)
  rw [← AlgebraicGeometry.Spec.map_comp]
  rfl

end

end GroupActions
