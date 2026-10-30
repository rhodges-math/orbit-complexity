import OrbitComplexity.SchubertGeometry.Parabolics.Geometry
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Partial flag and Schubert projections over the complex numbers

The complex specialization retains all the maps and compatibility equations.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions SchubertGeometry
noncomputable section
namespace SchubertOrbits

/-- The complete partial flag and Schubert projection clauses over the complex numbers. -/
theorem partial_flags_complex :
  ∀ (G : ReductiveGroupData ℂ) (J : Set G.rootBase.support),
    IsProper (partialFlagVariety G J).toSpec ∧
    (∃ n : ℕ, ∃ i : (partialFlagVariety G J).toOver ⟶
      (projectiveVariety ℂ (ULift (Fin n))).toOver, IsClosedImmersion i.left) ∧
    Surjective (partialFlagMorphism G J).left ∧
    IsProper (partialFlagMorphism G J).left ∧
    IsModHom (reductiveVariety G).toOver (partialFlagMorphism G J) ∧
    (∀ p : flagPoints G,
      Variety.mapPoints (partialFlagMorphism G J) (flagVarietyPointsEquiv G p) =
        partialFlagPointsEquiv G J (SchubertGeometry.partialFlagProjection G J p)) ∧
    ∀ w : G.weylGroup, IsMinimalRightParabolic G.rootBase J w →
      (∃ e : (schubertCell G w).toOver ≅ (partialSchubertCell G J w).toOver,
        e.hom = partialCellProjection G J w) ∧
      (∃ f : (schubertVariety G w).toOver ⟶ (partialSchubertVariety G J w).toOver,
        f ≫ partialSchubertInclusion G J w =
          schubertInclusion G w ≫ partialFlagMorphism G J ∧
        Surjective f.left ∧ IsProper f.left ∧
        ∃ p : (schubertVariety G w).scheme.PartialIso (partialSchubertVariety G J w).scheme,
          p.IsOver (schubertVariety G w).toSpec (partialSchubertVariety G J w).toSpec ∧
          p.source.ι ≫ f.left = p.iso.hom ≫ p.target.ι) ∧
      ((partialFlagMorphism G J).left ⁻¹' Set.range (partialSchubertInclusion G J w).left =
        Set.range (schubertInclusion G (w * longestParabolicElement G.rootBase J)).left) ∧
      ∃ e : (schubertVariety G (w * longestParabolicElement G.rootBase J)).scheme ≅
          CategoryTheory.Limits.pullback (partialFlagMorphism G J).left
            (partialSchubertInclusion G J w).left,
        e.hom ≫ CategoryTheory.Limits.pullback.fst (partialFlagMorphism G J).left
            (partialSchubertInclusion G J w).left =
          (schubertInclusion G (w * longestParabolicElement G.rootBase J)).left := by
  intro G J
  exact partialFlag_properties G J

end SchubertOrbits
