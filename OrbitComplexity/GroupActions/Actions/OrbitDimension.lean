import OrbitComplexity.GroupActions.Actions.OrbitFibreDimensions
import OrbitComplexity.GroupActions.Varieties.GenericBaseFibres

/-! # Orbit dimensions for irreducible group varieties

The generic fibre dimension formula for the orbit projection, together with translation
of its rational fibres, expresses the group dimension as orbit dimension plus stabilizer
dimension. The natural and integer formulas follow from the exact dimension casts.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver] [IrreducibleSpace H.scheme]

/-- The dimension of an irreducible group is orbit dimension plus stabilizer dimension. -/
theorem orbit_dimension_add (x : X.points) :
    H.dim = orbitDim H X x + (stabilizerVariety H X x).dim := by
  let O := orbitVariety H X x
  obtain ⟨U, hU, hd⟩ := Variety.exists_open_dim_add H O (orbitProjection H X x)
  have : JacobsonSpace O.scheme := LocallyOfFiniteType.jacobsonSpace O.toSpec
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hU U.isOpen.isLocallyClosed
  obtain ⟨p, hp⟩ := O.pointsEquivClosedPoints.surjective ⟨y, hc⟩
  have he : O.pointMap p = y := congrArg Subtype.val hp
  have h := hd y hy
  rw [orbitVariety_dim, ← he, ← orbitProjection_fibre_dim H X x p] at h
  exact h

/-- The natural dimension of the group is orbit dimension plus stabilizer dimension. -/
theorem orbitNatDim_add_stabilizer (x : X.points) :
    H.natDim = orbitNatDim H X x + (stabilizerVariety H X x).natDim := by
  have h := orbit_dimension_add H X x
  rw [← H.natDim_cast, ← orbitNatDim_cast H X x,
    ← (stabilizerVariety H X x).natDim_cast] at h
  have h' : (H.natDim : WithBot ℕ∞) =
      ((orbitNatDim H X x + (stabilizerVariety H X x).natDim : ℕ) : WithBot ℕ∞) := by
    simpa only [Nat.cast_add] using h
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp h')

end

end GroupActions
