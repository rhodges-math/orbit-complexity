import OrbitComplexity.SchubertGeometry.Cells.TorusComplexity
import OrbitComplexity.Paper.Heart.LeviComplexity

/-! # Levi complexity after passage to Schubert closures

The cell orbit comparison and torus-equivariant dense-open inclusion identify
Levi complexity with torus complexity of the minimal parabolic Schubert variety.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- Levi complexity equals torus complexity of the minimal parabolic Schubert variety. -/
theorem levi_complexity_eq_minimal (I : Set G.rootBase.support) (w : G.weylGroup)
    [ModObj (leviVariety G I).toOver (schubertVariety G w).toOver]
    [IsModHom (leviVariety G I).toOver (schubertInclusion G w)] :
    letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
        (schubertVariety G w).toOver :=
      inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
    complexity (leviGroupData G I) (schubertVariety G w) =
      torusComplexity G
        (schubertVariety G (leftParabolicRepresentative G.rootBase I w)) := by
  exact (levi_complexity_eq_torus G I w).trans
    (torus_cell_complexity G (leftParabolicRepresentative G.rootBase I w))

/-- The Levi-to-minimal-Schubert complexity comparison over the complex numbers. -/
theorem levi_complexity_eq_minimal_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup)
    [ModObj (leviVariety G I).toOver (schubertVariety G w).toOver]
    [IsModHom (leviVariety G I).toOver (schubertInclusion G w)] :
    letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
        (schubertVariety G w).toOver :=
      inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
    complexity (leviGroupData G I) (schubertVariety G w) =
      torusComplexity G
        (schubertVariety G (leftParabolicRepresentative G.rootBase I w)) :=
  levi_complexity_eq_minimal G I w

end SchubertOrbits
