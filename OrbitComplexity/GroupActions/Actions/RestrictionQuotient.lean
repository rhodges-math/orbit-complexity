import OrbitComplexity.GroupActions.Actions.RestrictionOrbits

/-! # Orbit quotients under surjective restriction

Scalar restriction along a group morphism surjective on rational points preserves the
orbit relation. The identity on representatives therefore gives an equivalence of orbit
quotient types.

## Main definitions

* `GroupActions.Variety.restrictionQuotientEquiv`: the equivalence of orbit quotients.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] {H G : GroupActions.Variety K} [GrpObj H.toOver]
  [GrpObj G.toOver] (f : H.toOver ⟶ G.toOver) [IsMonHom f]
  (hf : Function.Surjective (mapPoints f)) (X : GroupActions.Variety K)
  [ModObj G.toOver X.toOver]

/-- Surjective scalar restriction identifies the types of rational-point orbits. -/
def restrictionQuotientEquiv :
    let ordinaryQ := MulAction.orbitRel.Quotient G.points X.points
    letI := Mod.scalarRestriction f X.toOver
    ordinaryQ ≃ MulAction.orbitRel.Quotient H.points X.points := by
  let ordinaryQ := MulAction.orbitRel.Quotient G.points X.points
  letI := Mod.scalarRestriction f X.toOver
  refine Quotient.congrRight (fun a b ↦ ?_)
  change a ∈ MulAction.orbit G.points b ↔ a ∈ MulAction.orbit H.points b
  rw [restricted_orbit f hf X b]

end

end GroupActions.Variety
