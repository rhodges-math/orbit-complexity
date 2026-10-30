import OrbitComplexity.Paper.Heart.Embedding
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The heart as a subvariety of its Schubert cell

The closed cell inclusion and its flag image describe the heart defined by Vd wB.
-/

open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
namespace SchubertOrbits
universe u
/-- The heart is the locally closed flag image Vd wB, closed inside its Schubert cell. -/
theorem heart_definition {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (I : Set G.rootBase.support) (w : G.weylGroup) :
    IsPreimmersion (heartInclusion G I w).left ∧
      IsClosedImmersion (heartCellInclusion G I w).left ∧
      heartCellInclusion G I w ≫ schubertCellInclusion G w = heartInclusion G I w ∧
      (∀ q : (flagVariety G).points,
        q ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) ↔
          ∃ v ∈ Vd.points G I w,
            flagVarietyPointsEquiv G (flagProjection G (v * G.weylPoint w)) = q) :=
  ⟨inferInstance, inferInstance, heartCellInclusion_comp G I w, mem_heart_iff G I w⟩

/-- The closed heart and its exact flag image over the complex numbers. -/
theorem heart_definition_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup) :
    IsPreimmersion (heartInclusion G I w).left ∧
      IsClosedImmersion (heartCellInclusion G I w).left ∧
      heartCellInclusion G I w ≫ schubertCellInclusion G w = heartInclusion G I w ∧
      (∀ q : (flagVariety G).points,
        q ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) ↔
          ∃ v ∈ Vd.points G I w,
            flagVarietyPointsEquiv G (flagProjection G (v * G.weylPoint w)) = q) :=
  heart_definition G I w
end SchubertOrbits
