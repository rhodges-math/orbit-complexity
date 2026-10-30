import OrbitComplexity.Paper.Deodhar.ComponentActions
import OrbitComplexity.GroupActions.Actions.ImmersedOrbits

/-! # Orbit dimensions under component inclusions

The intrinsic component inclusion is a locally closed immersion. Its equivariance identifies
each component orbit with the same torus orbit in the flag variety and preserves its dimension.
-/

open CategoryTheory AlgebraicGeometry Topology ReductiveGroups SchubertGeometry GroupActions
namespace SchubertOrbits
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : BruhatIntervals.Subexpression word)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)

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

omit [IsAlgClosed K] [CharZero K] in
private instance locallyClosedImmersion (X : Variety K) (S : Set X.scheme)
    (hS : IsLocallyClosed S) : IsImmersion (X.locallyClosedInclusion S hS).left where
  isLocallyClosed_range := by rw [Variety.locallyClosedInclusion_range]; exact hS

private instance cellImmersion (w : G.weylGroup) :
    IsImmersion (schubertCellInclusion G w).left where
  isLocallyClosed_range := by
    rw [GroupActions.orbitInclusion_range]
    exact orbitImage_locallyClosed _ _ _

private theorem inclusionImmersion : IsImmersion (deodharInclusion G expression hred).left :=
  inferInstanceAs (IsImmersion
    ((deodharPrefixInclusion G expression hred word.length).left ≫
      (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take word.length))).left))

/-- A component torus orbit has the same natural dimension in the flag variety. -/
theorem deodhar_orbitNatDim (x : (deodharComponent G expression hred).points) :
    orbitNatDim (torusVariety G) (flagVariety G)
      (Variety.mapPoints (deodharInclusion G expression hred) x) =
        orbitNatDim (torusVariety G) (deodharComponent G expression hred) x := by
  have := inclusionImmersion G expression hred
  have h := orbit_image_dim (torusVariety G) (deodharComponent G expression hred)
    (flagVariety G) (deodharInclusion G expression hred) x
  rw [equivariant_orbit (deodharInclusion G expression hred) x] at h
  unfold orbitNatDim
  exact congrArg (fun d : WithBot ℕ∞ => (d.unbotD 0).toNat) h

end
end SchubertOrbits
