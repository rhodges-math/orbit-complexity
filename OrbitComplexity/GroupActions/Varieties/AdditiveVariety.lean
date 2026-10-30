import OrbitComplexity.GroupActions.Varieties.AffineGroup
import OrbitComplexity.GroupActions.Varieties.ReductiveVariety
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaClosedImmersion
import OrbitComplexity.ReductiveGroups.Groups.Cells.RankOneSweepClosed

/-! # Additive varieties and root morphisms

The rank-one symmetric Hopf algebra represents the additive line. Its coordinate morphisms
give algebraic root maps with the usual field-valued parameters.
-/

open CategoryTheory AlgebraicGeometry TauCeti

namespace GroupActions
noncomputable section
universe u
variable (K : Type u) [Field K]

/-- The additive group as an affine variety over the field. -/
abbrev additiveVariety : Variety K := affineVariety K (SymmetricAlgebra K K)

/-- Field elements give the usual parameter points of the additive variety. -/
def additivePointsEquiv : K ≃ (additiveVariety K).points where
  toFun t := affineGroupPointsMulEquiv K (SymmetricAlgebra K K)
    ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm (Multiplicative.ofAdd t))
  invFun x := Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)
    ((affineGroupPointsMulEquiv K (SymmetricAlgebra K K)).symm x))
  left_inv t := by simp
  right_inv x := by
    change affineGroupPointsMulEquiv K (SymmetricAlgebra K K)
      ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
        (AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)
          ((affineGroupPointsMulEquiv K (SymmetricAlgebra K K)).symm x))) = x
    rw [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

variable {K} (G : ReductiveGroups.ReductiveGroupData K)

/-- A coordinate additive-group map defines a morphism from the additive variety to the group. -/
def gaMorphism (φ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K) :
    (additiveVariety K).toOver ⟶ (reductiveVariety G).toOver :=
  (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom φ.toAlgHom).op

/-- The additive-group morphism has the given root parameter on rational points. -/
theorem gaMorphism_points (φ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K) (t : K) :
    Variety.mapPoints (gaMorphism G φ) (additivePointsEquiv K t) =
      reductivePointsEquiv G (ReductiveGroups.gaParameterPoint φ t) := by
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom
      ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
        (Multiplicative.ofAdd t)).ofConv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ.toAlgHom.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

end
end GroupActions
