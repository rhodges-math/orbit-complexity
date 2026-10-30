import OrbitComplexity.SchubertGeometry.Cells.RichardsonActions
import OrbitComplexity.GroupActions.Actions.ImmersedOrbits

/-! # Orbit dimensions in Richardson varieties

The torus-equivariant closed immersion of a Richardson variety into the flag variety
preserves the dimension of every orbit.
-/

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem equivariant_points {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (h : H.points) (x : X.points) :
    Variety.mapPoints f (h • x) = h • Variety.mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (h • x) ≫ f = Y.pointsEquivOverHom (h • Variety.mapPoints f x)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom h) (X.pointsEquivOverHom x)

omit [IsAlgClosed K] [CharZero K] in
private theorem equivariant_orbit {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (x : X.points) :
    Variety.mapPoints f '' MulAction.orbit H.points x =
      MulAction.orbit H.points (Variety.mapPoints f x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.mp hz
    rw [equivariant_points]
    exact MulAction.mem_orbit _ h
  · intro hy
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hy
    exact ⟨h • x, MulAction.mem_orbit _ h, (equivariant_points f h x).trans hh⟩

/-- A Richardson torus orbit has the same dimension in the ambient flag variety. -/
theorem richardsonInclusion_orbitNatDim (u v : G.weylGroup)
    (x : (richardsonVariety G u v).points) :
    orbitNatDim (torusVariety G) (flagVariety G)
      (Variety.mapPoints (richardsonInclusion G u v) x) =
        orbitNatDim (torusVariety G) (richardsonVariety G u v) x := by
  have h := orbit_image_dim (torusVariety G) (richardsonVariety G u v)
    (flagVariety G) (richardsonInclusion G u v) x
  rw [equivariant_orbit (richardsonInclusion G u v) x] at h
  unfold orbitNatDim
  exact congrArg (fun d : WithBot ℕ∞ => (d.unbotD 0).toNat) h

end
end SchubertGeometry
