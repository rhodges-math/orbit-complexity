import OrbitComplexity.GroupActions.Actions.OrbitDimension
import OrbitComplexity.GroupActions.Actions.IdentityOrbitDimension
import OrbitComplexity.GroupActions.Actions.IdentityStabilizer

/-! # Orbit dimension for algebraic groups

The identity component has the group dimension and the same orbit and stabilizer
dimensions. The irreducible-group dimension formula therefore extends to every group variety.

## Main results

* `GroupActions.dim_orbit`: orbit dimension is group dimension minus stabilizer dimension.
* `GroupActions.orbit_dimension_formula`: orbits are locally closed and have this dimension.

## References

* M. Brion, *Introduction to actions of algebraic groups*, Luminy lecture notes (2009),
  Proposition 1.11.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]

private theorem orbit_add_general (x : X.points) :
    H.dim = orbitDim H X x + (stabilizerVariety H X x).dim := by
  let := identityComponentAction H X
  have h := orbit_dimension_add (identityComponent H) X x
  rw [identityComponent_dim, identity_orbitDim, identity_stabilizer_dim] at h
  exact h

/-- The group dimension is orbit dimension plus stabilizer dimension. -/
theorem groupNatDim_eq_orbit_add (x : X.points) :
    H.natDim = orbitNatDim H X x + (stabilizerVariety H X x).natDim := by
  have : Nonempty H.scheme := ⟨H.pointMap 1⟩
  have h := orbit_add_general H X x
  rw [← H.natDim_cast, ← orbitNatDim_cast H X x,
    ← (stabilizerVariety H X x).natDim_cast] at h
  have h' : (H.natDim : WithBot ℕ∞) =
      ((orbitNatDim H X x + (stabilizerVariety H X x).natDim : ℕ) : WithBot ℕ∞) := by
    simpa only [Nat.cast_add] using h
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp h')

/-- Orbit dimension is group dimension minus stabilizer dimension. -/
theorem dim_orbit (x : X.points) :
    (orbitNatDim H X x : ℤ) = (H.natDim : ℤ) -
      ((stabilizerVariety H X x).natDim : ℤ) := by
  have h := congrArg (fun n : ℕ ↦ (n : ℤ)) (groupNatDim_eq_orbit_add H X x)
  rw [Nat.cast_add] at h
  exact eq_sub_iff_add_eq.mpr h.symm

/-- Orbits are locally closed, and their dimension is group dimension minus stabilizer dimension. -/
theorem orbit_dimension_formula (x : X.points) :
    IsLocallyClosed (MulAction.orbit H.points x) ∧
      (orbitNatDim H X x : ℤ) = (H.natDim : ℤ) -
        ((stabilizerVariety H X x).natDim : ℤ) :=
  ⟨orbit_locallyClosed H X x, dim_orbit H X x⟩

end

end GroupActions
