import OrbitComplexity.Paper.Heart.Equivariance
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The torus-equivariant heart isomorphism

The heart is stable under the ordinary torus action, and inverse parabolic
translation identifies it equivariantly with the twisted minimal Schubert cell.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u

/-- The heart is torus-stable and inverse parabolic translation is an equivariant isomorphism. -/
theorem heart_equivariant_iso {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (I : Set G.rootBase.support) (w : G.weylGroup) :
    (∀ (t : (torusVariety G).points) (q : (flagVariety G).points),
      q ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) →
        t • q ∈ Set.range (Variety.mapPoints (heartInclusion G I w))) ∧
    (letI := twistedAction G (leftParabolicFactor G.rootBase I w)⁻¹
      (schubertCell G (leftParabolicRepresentative G.rootBase I w))
     ∃ e : (heart G I w).toOver ≅
         (schubertCell G (leftParabolicRepresentative G.rootBase I w)).toOver,
       IsModHom (torusVariety G).toOver e.hom ∧
       e.hom ≫ schubertCellInclusion G (leftParabolicRepresentative G.rootBase I w) =
         heartInclusion G I w ≫
           (Variety.translationIso (reductiveVariety G) (flagVariety G)
             (reductivePointsMulEquiv G
               (G.weylPoint (leftParabolicFactor G.rootBase I w)))).inv ∧
       (∀ x : (heart G I w).points,
         Variety.mapPoints (schubertCellInclusion G
           (leftParabolicRepresentative G.rootBase I w)) (Variety.mapPoints e.hom x) =
           (reductivePointsMulEquiv G
             (G.weylPoint (leftParabolicFactor G.rootBase I w)))⁻¹ •
               Variety.mapPoints (heartInclusion G I w) x)) := by
  refine ⟨fun t q hq => heart_torus_stable G I w t hq, ?_⟩
  let := twistedAction G (leftParabolicFactor G.rootBase I w)⁻¹
    (schubertCell G (leftParabolicRepresentative G.rootBase I w))
  exact ⟨heartMinimalIso G I w, heartMinimalIso_isModHom G I w,
    heartMinimalIso_hom_comp G I w, heartMinimalIso_points G I w⟩

/-- The torus-equivariant heart isomorphism and its flag formula over the complex numbers. -/
theorem heart_equivariant_iso_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup) :
    (∀ (t : (torusVariety G).points) (q : (flagVariety G).points),
      q ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) →
        t • q ∈ Set.range (Variety.mapPoints (heartInclusion G I w))) ∧
    (letI := twistedAction G (leftParabolicFactor G.rootBase I w)⁻¹
      (schubertCell G (leftParabolicRepresentative G.rootBase I w))
     ∃ e : (heart G I w).toOver ≅
         (schubertCell G (leftParabolicRepresentative G.rootBase I w)).toOver,
       IsModHom (torusVariety G).toOver e.hom ∧
       e.hom ≫ schubertCellInclusion G (leftParabolicRepresentative G.rootBase I w) =
         heartInclusion G I w ≫
           (Variety.translationIso (reductiveVariety G) (flagVariety G)
             (reductivePointsMulEquiv G
               (G.weylPoint (leftParabolicFactor G.rootBase I w)))).inv ∧
       (∀ x : (heart G I w).points,
         Variety.mapPoints (schubertCellInclusion G
           (leftParabolicRepresentative G.rootBase I w)) (Variety.mapPoints e.hom x) =
           (reductivePointsMulEquiv G
             (G.weylPoint (leftParabolicFactor G.rootBase I w)))⁻¹ •
               Variety.mapPoints (heartInclusion G I w) x)) :=
  heart_equivariant_iso G I w

end SchubertOrbits
