import Batteries.Tactic.Lint
import OrbitComplexity.GroupActions.Varieties.Factorization
import OrbitComplexity.SchubertGeometry.Cells.Richardson

/-!
# Factoring reduced root curves through the original Richardson target

A reduced source morphism whose image satisfies the two original closed
Schubert conditions factors through the original Richardson inclusion. This
generic factorization does not construct the arbitrary-root projective curve;
that missing geometric construction is recorded below.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace SchubertGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- Factor a reduced-source morphism through the original Richardson target
using its two closed Schubert image conditions. -/
def richardsonCurveFactor (a b : G.weylGroup) {Y : Scheme.{u}} [IsReduced Y]
    (c : Y ⟶ (flagVariety G).scheme)
    (hordinary : Set.range c ⊆ Set.range (schubertInclusion G b).left)
    (hopposite : Set.range c ⊆ Set.range (oppositeSchubertInclusion G a).left) :
    Y ⟶ (richardsonVariety G a b).scheme :=
  GroupActions.liftPreimmersion (richardsonInclusion G a b).left c (by
    rw [richardsonInclusion_range]
    exact fun z hz => ⟨hordinary hz, hopposite hz⟩)

/-- The factorization retains the original flag morphism. -/
theorem richardsonCurveFactor_comp (a b : G.weylGroup)
    {Y : Scheme.{u}} [IsReduced Y]
    (c : Y ⟶ (flagVariety G).scheme)
    (hordinary : Set.range c ⊆ Set.range (schubertInclusion G b).left)
    (hopposite : Set.range c ⊆ Set.range (oppositeSchubertInclusion G a).left) :
    richardsonCurveFactor G a b c hordinary hopposite ≫
        (richardsonInclusion G a b).left = c :=
  GroupActions.liftPreimmersion_fac _ _ _

-- RootCurveParameters constructs the specified general-root SL2 maps.
-- RootCurveGluing constructs the projective curve with both Weyl endpoints;
-- RootCurveContainment proves both image certificates and uses this factor.
-- CoverRoots supplies the positive root for every intrinsic Bruhat cover.
-- These downstream files are kept out of this generic factorization import.

end SchubertGeometry
