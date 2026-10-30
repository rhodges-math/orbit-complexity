import OrbitComplexity.GroupActions.Actions.Orbits
import Mathlib.Order.Lattice.Nat

/-! # Minimum orbit codimension

The codimensions of rational-point orbits are nonnegative integers. Their minimum is
attained on a nonempty variety over an algebraically closed field.

## Main definitions

* `GroupActions.minOrbitCodim`: the minimum orbit codimension of an algebraic action.

## Main results

* `GroupActions.minOrbitCodim_le`: the minimum bounds every orbit codimension.
* `GroupActions.exists_orbitCodim_eq`: an orbit attains the minimum.
* `GroupActions.minOrbitCodim_isLeast`: the minimum is the least integer orbit codimension.

## Implementation notes

The minimum is a natural number; orbit codimensions are integers.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] (H X : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]

/-- The minimum of the codimensions of the orbits of an algebraic action. -/
def minOrbitCodim : ℕ := sInf (Set.range fun x : X.points ↦ (orbitCodim H X x).toNat)

/-- The natural minimum is a lower bound for every integer orbit codimension. -/
theorem minOrbitCodim_le (x : X.points) : (minOrbitCodim H X : ℤ) ≤ orbitCodim H X x := by
  have h : minOrbitCodim H X ≤ (orbitCodim H X x).toNat := Nat.sInf_le ⟨x, rfl⟩
  exact (Int.ofNat_le.mpr h).trans_eq (Int.toNat_of_nonneg (orbitCodim_nonneg H X x))

private theorem points_nonempty [IsAlgClosed K] [Nonempty X.scheme] : Nonempty X.points := by
  have : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  obtain ⟨x, _, hxc⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := X.scheme))
    isClosed_univ.isLocallyClosed
  exact ⟨X.pointsEquivClosedPoints.symm ⟨x, hxc⟩⟩

/-- An orbit of a nonempty variety over an algebraically closed field attains minimum
codimension. -/
theorem exists_orbitCodim_eq [IsAlgClosed K] [Nonempty X.scheme] :
    ∃ x : X.points, orbitCodim H X x = (minOrbitCodim H X : ℤ) := by
  have : Nonempty X.points := points_nonempty X
  obtain ⟨x, hx⟩ := Nat.sInf_mem
    (Set.range_nonempty (fun x : X.points ↦ (orbitCodim H X x).toNat))
  refine ⟨x, ?_⟩
  calc
    orbitCodim H X x = ((orbitCodim H X x).toNat : ℤ) :=
      (Int.toNat_of_nonneg (orbitCodim_nonneg H X x)).symm
    _ = (minOrbitCodim H X : ℤ) := congrArg (fun n : ℕ ↦ (n : ℤ)) hx

/-- The natural minimum, cast to the integers, is the least integer orbit codimension. -/
theorem minOrbitCodim_isLeast [IsAlgClosed K] [Nonempty X.scheme] :
    IsLeast (Set.range (orbitCodim H X)) (minOrbitCodim H X : ℤ) := by
  refine ⟨exists_orbitCodim_eq H X, ?_⟩
  rintro n ⟨x, rfl⟩
  exact minOrbitCodim_le H X x

end

end GroupActions
