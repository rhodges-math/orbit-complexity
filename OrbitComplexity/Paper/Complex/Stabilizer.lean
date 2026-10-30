import OrbitComplexity.SchubertGeometry.Parabolics.Stabilizer
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Complex Schubert stabilizers

The usual Schubert stabilizer is the standard parabolic of the left descents and supplies
the inherited actions of all standard Levi subgroups at those descents.
-/

namespace SchubertOrbits
open ReductiveGroups SchubertGeometry GroupActions CategoryTheory
open scoped Pointwise

/-- The complex Schubert stabilizer and its prescribed algebraic Levi restrictions. -/
theorem schubert_stabilizer_complex (G : ReductiveGroupData ℂ) (w : G.weylGroup) :
    (MulAction.stabilizer G.points ((flagVarietyPointsEquiv G) ⁻¹'
      Set.range (Variety.mapPoints (schubertInclusion G w))) =
      standardParabolicPoints G
        (BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w)) ∧
      ∀ I : Set G.rootBase.support,
        I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w →
        ∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
          letI := a
          IsModHom (leviVariety G I).toOver (schubertInclusion G w) :=
  schubert_stabilizer_levi G w

end SchubertOrbits
