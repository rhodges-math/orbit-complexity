import OrbitComplexity.GroupActions.Actions.Restriction
import OrbitComplexity.GroupActions.Complexity.OrbitCodimension

/-! # Orbits under surjective restriction

Restricting an action along a group morphism that is surjective on rational points
preserves its orbits, dimensions, codimensions, and minimum orbit codimension.

## Main results

* `GroupActions.Variety.restricted_orbit`: surjective restriction preserves orbits.
* `GroupActions.Variety.restricted_minOrbitCodim`: the minimum is preserved.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] {H G : GroupActions.Variety K} [GrpObj H.toOver]
  [GrpObj G.toOver] (f : H.toOver ⟶ G.toOver) [IsMonHom f]
  (hf : Function.Surjective (mapPoints f)) (X : GroupActions.Variety K)
  [ModObj G.toOver X.toOver]

include hf

/-- Surjective restriction of an algebraic action preserves each rational-point orbit. -/
theorem restricted_orbit (x : X.points) :
    letI := Mod.scalarRestriction f X.toOver
    MulAction.orbit H.points x = MulAction.orbit G.points x := by
  let := Mod.scalarRestriction f X.toOver
  ext y
  constructor
  · intro hy
    obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    rw [restricted_smul]
    exact MulAction.mem_orbit x _
  · intro hy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
    obtain ⟨h, hh⟩ := hf g
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨h, ?_⟩
    rw [restricted_smul, hh, hg]

/-- Surjective restriction preserves orbit dimension. -/
theorem restricted_orbitDim (x : X.points) :
    letI := Mod.scalarRestriction f X.toOver
    orbitDim H X x = orbitDim G X x := by
  let := Mod.scalarRestriction f X.toOver
  unfold orbitDim
  rw [restricted_orbit f hf X x]

/-- Surjective restriction preserves integer orbit codimension. -/
theorem restricted_orbitCodim (x : X.points) :
    letI := Mod.scalarRestriction f X.toOver
    orbitCodim H X x = orbitCodim G X x := by
  let := Mod.scalarRestriction f X.toOver
  unfold orbitCodim orbitNatDim
  rw [restricted_orbitDim f hf X x]

/-- Surjective restriction preserves the minimum orbit codimension. -/
theorem restricted_minOrbitCodim :
    letI := Mod.scalarRestriction f X.toOver
    minOrbitCodim H X = minOrbitCodim G X := by
  let := Mod.scalarRestriction f X.toOver
  have h : orbitCodim H X = orbitCodim G X := funext (restricted_orbitCodim f hf X)
  unfold minOrbitCodim
  rw [h]

end

end GroupActions.Variety
