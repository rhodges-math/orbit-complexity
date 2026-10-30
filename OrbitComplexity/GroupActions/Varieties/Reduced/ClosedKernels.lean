import OrbitComplexity.GroupActions.Varieties.Subvarieties
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! Kernel comparison for reduced closed intersections. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace GroupActions

/-- The ideal sheaf of a reduced closed subscheme is radical. -/
theorem closed_ker_radical {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [IsReduced X] : f.ker.radical = f.ker := by
  ext U : 2
  simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  exact Ideal.radical_eq_iff.mpr
    ((RingHom.ker_isRadical_iff_reduced_of_surjective
      (Scheme.Hom.app_surjective f U.1 U.2)).mpr inferInstance)

/-- Reduced closed subschemes with the same underlying closed set have the same
ideal sheaf in the ambient scheme. -/
theorem closed_ker_eq_of_reduced_range {X Y Z : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion f] [IsClosedImmersion g]
    [IsReduced X] [IsReduced Y] (h : Set.range f = Set.range g) : f.ker = g.ker := by
  have hs : f.ker.support = g.ker.support := by
    apply SetLike.coe_injective
    rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker, h]
  calc
    f.ker = f.ker.radical := (closed_ker_radical f).symm
    _ = Scheme.IdealSheafData.vanishingIdeal f.ker.support :=
      Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = Scheme.IdealSheafData.vanishingIdeal g.ker.support := congrArg _ hs
    _ = g.ker.radical := Scheme.IdealSheafData.vanishingIdeal_support
    _ = g.ker := closed_ker_radical g

end GroupActions
