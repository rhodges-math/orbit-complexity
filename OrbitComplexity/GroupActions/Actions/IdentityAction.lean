import OrbitComplexity.GroupActions.Actions.IdentityGroup
import OrbitComplexity.GroupActions.Actions.ComponentDimensions
import OrbitComplexity.GroupActions.Actions.Restriction
import OrbitComplexity.GroupActions.Actions.Orbits

/-! # Restriction to the identity component

An algebraic action restricts to the identity component. Finitely many translations of
its orbits cover the orbits of the whole group.

## Main definitions

* `GroupActions.identityComponentAction`: the action restricted to the identity component.

## Main results

* `GroupActions.identity_orbitMorphism`: the restricted orbit map factors the original one.
* `GroupActions.exists_finite_orbit_union`: an orbit is a finite union of translated orbits.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]

/-- The action restricted along the identity-component inclusion. -/
@[instance_reducible]
def identityComponentAction : ModObj (identityComponent H).toOver X.toOver :=
  Mod.scalarRestriction (identityInclusion H) X.toOver

attribute [local instance] identityComponentAction

/-- The identity-component action agrees with the ambient action after inclusion. -/
theorem identity_smul (h : (identityComponent H).points) (x : X.points) :
    h • x = Variety.mapPoints (identityInclusion H) h • x :=
  Variety.restricted_smul (identityInclusion H) X h x

/-- The restricted orbit morphism factors through the identity-component inclusion. -/
theorem identity_orbitMorphism (x : X.points) :
    Variety.orbitMorphism (identityComponent H) X x =
      identityInclusion H ≫ Variety.orbitMorphism H X x := by
  apply Variety.mapPoints_injective
  funext h
  rw [Variety.mapPoints_orbitMorphism, Variety.mapPoints_comp,
    Variety.mapPoints_orbitMorphism]
  exact identity_smul H X h x

/-- An orbit is a finite union of translates of the identity-component orbit. -/
theorem exists_finite_orbit_union (x : X.points) :
    ∃ s : Finset H.points, MulAction.orbit H.points x =
      ⋃ h ∈ s, Variety.mapPoints (Variety.translateMorphism H X h) ''
        MulAction.orbit (identityComponent H).points x := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_components H
  refine ⟨s, Set.Subset.antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨p, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    obtain ⟨h, hhs, hhp⟩ := hs (H.pointMap p)
    obtain ⟨q, hq⟩ := exists_identity_translate H h p hhp
    apply Set.mem_iUnion.mpr
    refine ⟨h, Set.mem_iUnion.mpr ⟨hhs, ?_⟩⟩
    refine ⟨q • x, MulAction.mem_orbit x q, ?_⟩
    rw [Variety.mapPoints_translateMorphism, identity_smul, ← mul_smul, hq]
  · intro y hy
    obtain ⟨h, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨-, q, hq, rfl⟩ := Set.mem_iUnion.mp hy
    obtain ⟨p, rfl⟩ := MulAction.mem_orbit_iff.mp hq
    rw [Variety.mapPoints_translateMorphism, identity_smul, ← mul_smul]
    exact MulAction.mem_orbit x _

end

end GroupActions
