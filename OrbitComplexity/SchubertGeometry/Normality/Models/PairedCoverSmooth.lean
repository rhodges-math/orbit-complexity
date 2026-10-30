import OrbitComplexity.GroupActions.Actions.IntersectionSmooth
import OrbitComplexity.SchubertGeometry.BSDH.Paired

/-! # Smooth Borel-product covers of paired BSDH sources

The ordinary and opposite endpoint actions satisfy the equivariance identities
required by the transverse flag action, giving smoothness before reduction.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The Borel-product cover of the raw paired endpoint source is smooth by
the transverse flag action, with no normality or target-splitting input. -/
theorem pairedBSDHCover_smooth (a b : List G.rootBase.support) :
    Smooth ((((borelVariety G).toOver ⊗ (oppositeBorelVariety G).toOver) ⊗
      pairedBSDHSource G a b).hom) := by
  let := bsdhBorelAction G a
  let := bsdhOppositeAction G b
  have := bsdhBorelEquivariant G a
  have := bsdhOppositeEquivariant G b
  have : Smooth (bsdhVariety G a).toOver.hom := bsdh_smooth G a
  have : Smooth (bsdhVariety G b).toOver.hom := bsdh_smooth G b
  have : Smooth (transverseAction (borelVariety G).toOver
      (oppositeBorelVariety G).toOver (flagVariety G).toOver).left :=
    flagTransverseAction_smooth G
  exact equivariantIntersection_smooth (borelVariety G).toOver
    (oppositeBorelVariety G).toOver (flagVariety G).toOver
    (bsdhVariety G a).toOver (bsdhVariety G b).toOver
    (Over.homMk (bsdhMap G a) rfl) (bsdhOppositeEndpoint G b)

end
end SchubertGeometry
