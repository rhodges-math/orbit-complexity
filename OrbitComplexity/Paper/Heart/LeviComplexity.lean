import OrbitComplexity.SchubertGeometry.Levi.CellComplexity
import OrbitComplexity.Paper.Heart.LeviMinimum
import OrbitComplexity.GroupActions.Complexity.Toric
import Mathlib.Analysis.Complex.Polynomial.Basic
/-! # Complexity after parabolic reduction

Restricting a Levi action to its Borel and the open Schubert cell, then comparing
heart orbits, gives the torus complexity of the minimal parabolic cell.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)
/-- Levi complexity of a Schubert variety equals torus complexity of its minimal parabolic cell. -/
theorem levi_complexity_eq_torus (I : Set G.rootBase.support) (w : G.weylGroup)
    [ModObj (leviVariety G I).toOver (schubertVariety G w).toOver]
    [IsModHom (leviVariety G I).toOver (schubertInclusion G w)] :
    letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
        (schubertVariety G w).toOver :=
      inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
    complexity (leviGroupData G I) (schubertVariety G w) =
      torusComplexity G
        (schubertCell G (leftParabolicRepresentative G.rootBase I w)) := by
  exact (levi_schubert_complexity_cell G I w).trans
    (levi_cell_minOrbitCodim G I w ⟨inferInstance, inferInstance⟩)
/-- The Levi-to-torus complexity equality over the complex numbers. -/
theorem levi_complexity_eq_torus_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup)
    [ModObj (leviVariety G I).toOver (schubertVariety G w).toOver]
    [IsModHom (leviVariety G I).toOver (schubertInclusion G w)] :
    letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
        (schubertVariety G w).toOver :=
      inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
    complexity (leviGroupData G I) (schubertVariety G w) =
      torusComplexity G
        (schubertCell G (leftParabolicRepresentative G.rootBase I w)) :=
  levi_complexity_eq_torus G I w
end SchubertOrbits
