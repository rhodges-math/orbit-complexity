import Batteries.Tactic.Lint
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import OrbitComplexity.SchubertGeometry.Cells.CellChart
import OrbitComplexity.SchubertGeometry.Cells.Actions
import OrbitComplexity.GroupActions.Tori.RootConjugation
import OrbitComplexity.GroupActions.Actions.EquivariantPoints
import OrbitComplexity.GroupActions.Actions.EquivariantMono

/-!
# Equivariance of the original root-cell chart

The conjugation orbit map is equivariant on rational points by a coset identity
in an arbitrary group. The existing reduced-variety equivariance theorem then
proves the equality of action morphisms on the universal torus product. Its
consequence is valid after pullback to arbitrary, possibly nonreduced schemes.

-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section

namespace SchubertGeometry.CellContraction

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

universe u

/-- Normalizing the stabilizing subgroup makes conjugation and left action
agree on the orbit through the chosen coset. -/
theorem conjugate_coset_eq {H : Type u} [Group H] (B T : Subgroup H)
    (hTB : T ≤ B) (n t x : H)
    (hn : n ∈ Subgroup.normalizer (T : Set H)) (ht : t ∈ T) :
    (QuotientGroup.mk ((t * x * t⁻¹) * n) : H ⧸ B) =
      QuotientGroup.mk (t * (x * n)) := by
  apply QuotientGroup.eq.mpr
  have hc : n⁻¹ * t * n ∈ T :=
    ((Subgroup.mem_set_normalizer_iff'').mp hn t).mp ht
  have he : ((t * x * t⁻¹) * n)⁻¹ * (t * (x * n)) = n⁻¹ * t * n := by
    group
  rw [he]
  exact hTB hc

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- Root conjugation and the original torus flag action agree as morphisms. -/
theorem schubertRootMorphism_equivariant (w : G.weylGroup) :
    let := GroupActions.rootConjugationAction G
      (ReductiveGroups.leftRootInversionIndices G.rootBase w)
      (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
    IsModHom (GroupActions.torusVariety G).toOver (schubertRootMorphism G w) := by
  let := GroupActions.rootConjugationAction G
    (ReductiveGroups.leftRootInversionIndices G.rootBase w)
    (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
  apply GroupActions.Variety.isModHom_of_points
    (GroupActions.torusVariety G) (schubertUnipotent G w) (flagVariety G)
  intro t x
  simp only [schubertRootMorphism_points,
    GroupActions.rootConjugationAction_smul, torusFlag_smul,
    ← flagProjection_smul]
  apply congrArg (flagVarietyPointsEquiv G)
  exact conjugate_coset_eq G.borelPoints G.torusPoints G.torus_le_borel
    (G.weylPoint w) (GroupActions.torusPointsMulEquiv G t)
    (GroupActions.rootSubsetPointsMulEquiv G _ _ x)
    (G.weylPoint_mem_normalizer w) (GroupActions.torusPointsMulEquiv G t).property

/-- The specified affine-cell isomorphism is torus equivariant. -/
theorem schubertCellIso_equivariant (w : G.weylGroup) :
    let := GroupActions.rootConjugationAction G
      (ReductiveGroups.leftRootInversionIndices G.rootBase w)
      (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
    IsModHom (GroupActions.torusVariety G).toOver (schubertCellIso G w).hom := by
  let := GroupActions.rootConjugationAction G
    (ReductiveGroups.leftRootInversionIndices G.rootBase w)
    (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
  let := schubertRootMorphism_equivariant G w
  let : Mono (schubertCellInclusion G w) :=
    Over.mono_of_mono_left (schubertCellInclusion G w)
  let : IsModHom (GroupActions.torusVariety G).toOver
      ((schubertCellIso G w).hom ≫ schubertCellInclusion G w) := by
    rw [schubertCellIso_hom_comp]
    exact schubertRootMorphism_equivariant G w
  exact GroupActions.isModHom_of_comp_mono
    (schubertCellIso G w).hom (schubertCellInclusion G w)

end SchubertGeometry.CellContraction
