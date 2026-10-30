import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Power
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.RegularAction

/-! # The regular determinant-power function and its Borel covariance -/

open AlgebraicGeometry CategoryTheory ReductiveGroups TauCeti GroupActions WithConv

noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [CharZero K] in
private theorem borelReduced : IsReduced (G.borelAlgebra.obj : Type u) := by
  let : Algebra.Smooth K (G.borelAlgebra.obj : Type u) := G.borel_smooth
  exact TauCeti.isReduced_of_smooth K (G.borelAlgebra.obj : Type u)

attribute [local instance] borelReduced

private def powerCoordinate (N : ℕ) : SymmetricAlgebra K K →ₐ[K] G.coordinateAlgebra :=
  SymmetricAlgebra.lift (LinearMap.toSpanSingleton K _ (positiveDetPower G N))

/-- The same determinant power defines a regular morphism from the group to the affine line. -/
def positiveDetPowerMorphism (N : ℕ) :
    (reductiveVariety G).toOver ⟶ (additiveVariety K).toOver :=
  (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (powerCoordinate G N)).op

/-- On group points the regular morphism evaluates the original determinant power. -/
theorem positiveDetPowerMorphism_points (N : ℕ) (g : G.points) :
    Variety.mapPoints (positiveDetPowerMorphism G N) (reductivePointsEquiv G g) =
      additivePointsEquiv K (g.ofConv (positiveDetPower G N)) := by
  let q := ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd (g.ofConv (positiveDetPower G N)))).ofConv
  have hgen : (g.ofConv.comp (powerCoordinate G N)) (SymmetricAlgebra.ι K K 1) =
      q (SymmetricAlgebra.ι K K 1) := by
    simp only [AlgHom.comp_apply, powerCoordinate, SymmetricAlgebra.lift_ι_apply,
      LinearMap.toSpanSingleton_apply, one_smul, q,
      AdditiveGroup.gaPointsMulEquiv_symm_apply_ι, toAdd_ofAdd]
  have he : g.ofConv.comp (powerCoordinate G N) = q := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro a
    have hι : SymmetricAlgebra.ι K K a = a • SymmetricAlgebra.ι K K 1 := by
      simpa only [smul_eq_mul, mul_one] using
        (map_smul (SymmetricAlgebra.ι K K) a (1 : K))
    change (g.ofConv.comp (powerCoordinate G N)) (SymmetricAlgebra.ι K K a) =
      q (SymmetricAlgebra.ι K K a)
    rw [hι, map_smul, map_smul, hgen]
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (powerCoordinate G N).toRingHom) =
    Spec.map (CommRingCat.ofHom q.toRingHom)
  rw [← Spec.map_comp]
  exact congrArg (fun f : SymmetricAlgebra K K →ₐ[K] K =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) he

private theorem borel_power_value (N : ℕ) (b : (borelVariety G).points) :
    (borelPointsMulEquiv G b : G.points).ofConv (positiveDetPower G N) =
      (ProjectiveLine.borelCharacterUnit G (G.positiveRootCharacter ^ N)
        ((affineGroupPointsMulEquiv K G.borelAlgebra).symm b) : K) := by
  rw [borelPointsMulEquiv_coe]
  change (affinePointsEquiv.symm b)
      (((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom)
        (positiveDetPower G N)) = _
  rw [positiveDetPower_borel_restriction G N]
  rfl

/-- Right multiplication by a Borel point has the full character of the same power. -/
theorem positiveDetPower_right_borel (N : ℕ) (g : G.points)
    (b : (borelVariety G).points) :
    (g * (borelPointsMulEquiv G b : G.points)).ofConv (positiveDetPower G N) =
      (ProjectiveLine.borelCharacterUnit G (G.positiveRootCharacter ^ N)
        ((affineGroupPointsMulEquiv K G.borelAlgebra).symm b) : K) *
          g.ofConv (positiveDetPower G N) := by
  have hb := (borelPointsMulEquiv G b).property
  have hp : (g * (borelPointsMulEquiv G b : G.points)).ofConv (positiveDetPower G N) =
      (borelPointsMulEquiv G b : G.points).ofConv (positiveDetPower G N) *
        g.ofConv (positiveDetPower G N) := by
    simp only [positiveDetPower, map_pow, positiveDet_right_borel G g _ hb, mul_pow]
  exact hp.trans (congrArg (fun a : K => a * g.ofConv (positiveDetPower G N))
    (borel_power_value G N b))

end SchubertGeometry.DeterminantSection
