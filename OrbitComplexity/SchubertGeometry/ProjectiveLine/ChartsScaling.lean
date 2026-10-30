import OrbitComplexity.GroupActions.Varieties.AdditiveVariety
import OrbitComplexity.GroupActions.Varieties.AffineMorphisms

/-! # Scalar changes of additive coordinates

Multiplication by a nonzero scalar is an automorphism of the additive variety.
Its symmetric-algebra morphism gives the usual scalar multiplication on rational points.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions TauCeti
universe u
variable {K : Type u} [Field K]
private def scaleCoordinate (c : K) : SymmetricAlgebra K K →ₐ[K] SymmetricAlgebra K K :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι K K).comp (c • LinearMap.id))
private theorem scaleCoordinate_ι (c t : K) :
    scaleCoordinate c (SymmetricAlgebra.ι K K t) = SymmetricAlgebra.ι K K (c * t) := by
  simp only [scaleCoordinate, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
private theorem scaleCoordinate_comp (c d : K) :
    (scaleCoordinate c).comp (scaleCoordinate d) = scaleCoordinate (c * d) := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro t
  change scaleCoordinate c (scaleCoordinate d (SymmetricAlgebra.ι K K t)) =
    scaleCoordinate (c * d) (SymmetricAlgebra.ι K K t)
  rw [scaleCoordinate_ι, scaleCoordinate_ι, scaleCoordinate_ι]
  congr 1
  ring
private theorem scaleCoordinate_one : scaleCoordinate (1 : K) = AlgHom.id K _ := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro t
  change scaleCoordinate (1 : K) (SymmetricAlgebra.ι K K t) = SymmetricAlgebra.ι K K t
  rw [scaleCoordinate_ι, one_mul]
private def scaleCoordinateEquiv (c : K) (hc : c ≠ 0) :
    SymmetricAlgebra K K ≃ₐ[K] SymmetricAlgebra K K :=
  AlgEquiv.ofAlgHom (scaleCoordinate c) (scaleCoordinate c⁻¹)
    (by rw [scaleCoordinate_comp, mul_inv_cancel₀ hc, scaleCoordinate_one])
    (by rw [scaleCoordinate_comp, inv_mul_cancel₀ hc, scaleCoordinate_one])
/-- A nonzero scalar multiplies the additive coordinate by a variety automorphism. -/
def additiveScaleIso (c : K) (hc : c ≠ 0) :
    (additiveVariety K).toOver ≅ (additiveVariety K).toOver :=
  (algSpec (CommRingCat.of K)).mapIso (CommAlgCat.isoMk (scaleCoordinateEquiv c hc)).op
private theorem additivePoint_coordinate (t : K) :
    (affineVarietyPointsEquiv K (SymmetricAlgebra K K)) (additivePointsEquiv K t) =
      ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
        (Multiplicative.ofAdd t)).ofConv := by
  change affinePointsEquiv.symm (affinePointsEquiv _) = _
  exact Equiv.symm_apply_apply _ _
/-- The scalar automorphism multiplies the canonical rational parameter. -/
theorem additiveScaleIso_points (c : K) (hc : c ≠ 0) (t : K) :
    Variety.mapPoints (additiveScaleIso c hc).hom (additivePointsEquiv K t) =
      additivePointsEquiv K (c * t) := by
  let p := ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd t)).ofConv
  have ht : additivePointsEquiv K t = (affineVarietyPointsEquiv K _).symm p := by
    apply (affineVarietyPointsEquiv K _).injective
    exact (additivePoint_coordinate t).trans (Equiv.apply_symm_apply _ _).symm
  rw [ht]
  change Variety.mapPoints (affineMorphism (scaleCoordinate c))
    ((affineVarietyPointsEquiv K _).symm p) = _
  rw [affineMorphism_points]
  apply (affineVarietyPointsEquiv K _).injective
  rw [Equiv.apply_symm_apply, additivePoint_coordinate]
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro a
  change p (scaleCoordinate c (SymmetricAlgebra.ι K K a)) =
    ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
      (Multiplicative.ofAdd (c * t))).ofConv (SymmetricAlgebra.ι K K a)
  rw [scaleCoordinate_ι]
  have hι (z : K) : SymmetricAlgebra.ι K K z = z • SymmetricAlgebra.ι K K 1 := by
    simpa only [smul_eq_mul, mul_one] using (map_smul (SymmetricAlgebra.ι K K) z (1 : K))
  rw [hι, map_smul, hι a, map_smul]
  simp only [p, AdditiveGroup.gaPointsMulEquiv_symm_apply_ι,
    smul_eq_mul]
  change (c * a) * t = a * (c * t)
  ring
end SchubertGeometry
