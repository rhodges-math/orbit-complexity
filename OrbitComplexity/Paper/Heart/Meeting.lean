import OrbitComplexity.SchubertGeometry.Levi.Cells
import OrbitComplexity.Paper.Heart.Dynamics
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.Longest
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Levi--Borel orbits meet the heart

The inverse of the parabolic unipotent factor moves a Schubert-cell point into
the heart, and that factor belongs to the standard Levi--Borel intersection.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u

/-- Every Levi--Borel orbit in a Schubert cell meets its parabolic heart. -/
theorem leviBorel_orbit_meets_heart {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (I : Set G.rootBase.support) (w : G.weylGroup)
    (q : (schubertCell G w).points) :
    ∃ b : (leviBorelVariety G I).points,
      Variety.mapPoints (schubertCellInclusion G w) (b • q) ∈
        Set.range (Variety.mapPoints (heartInclusion G I w)) := by
  obtain ⟨u, hu, hheart⟩ := exists_parabolic_smul_heart G I w
    (Variety.mapPoints (schubertCellInclusion G w) q) ⟨q, rfl⟩
  have huBL : u ∈ G.leviBorelPoints I := G.rootSubsetPoints_le_leviBorel I _ _
    (parabolic_inversions_subset G.rootBase I _ (leftParabolicFactor_mem G.rootBase I w)) hu
  let b : (leviBorelVariety G I).points := (leviBorelPointsMulEquiv G I).symm ⟨u, huBL⟩
  refine ⟨b, ?_⟩
  rw [leviBorelCell_smul, leviBorelFlag_smul]
  have he : (leviBorelPointsMulEquiv G I b : G.points) = u := by
    exact congrArg Subtype.val ((leviBorelPointsMulEquiv G I).apply_symm_apply ⟨u, huBL⟩)
  simpa only [he] using hheart

/-- Every complex Levi--Borel Schubert-cell orbit meets its parabolic heart. -/
theorem leviBorel_orbit_meets_heart_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup) (q : (schubertCell G w).points) :
    ∃ b : (leviBorelVariety G I).points,
      Variety.mapPoints (schubertCellInclusion G w) (b • q) ∈
        Set.range (Variety.mapPoints (heartInclusion G I w)) :=
  leviBorel_orbit_meets_heart G I w q

end SchubertOrbits
