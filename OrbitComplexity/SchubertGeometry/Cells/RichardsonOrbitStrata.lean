import OrbitComplexity.SchubertGeometry.Cells.RichardsonOrbitDimensions
import OrbitComplexity.SchubertGeometry.Cells.RichardsonStrata

/-! # Torus orbits across Richardson strata

The Bruhat decompositions place every Richardson point in an open Richardson stratum.
Equivariant immersions preserve the dimension of the common orbit in the flag variety.
-/

open CategoryTheory AlgebraicGeometry Topology GroupActions ReductiveGroups
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private instance richardson_immersion (a b : G.weylGroup) :
    IsImmersion (richardsonCellInclusion G a b).left where
  isLocallyClosed_range := by
    rw [richardsonCellInclusion_range, GroupActions.orbitInclusion_range,
      GroupActions.orbitInclusion_range]
    exact (orbitImage_locallyClosed _ _ _).inter (orbitImage_locallyClosed _ _ _)

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

private theorem cell_orbit_dimension (a b : G.weylGroup)
    (x : (richardsonCell G a b).points) :
    orbitNatDim (torusVariety G) (flagVariety G)
      (Variety.mapPoints (richardsonCellInclusion G a b) x) =
        orbitNatDim (torusVariety G) (richardsonCell G a b) x := by
  have h := orbit_image_dim (torusVariety G) (richardsonCell G a b)
    (flagVariety G) (richardsonCellInclusion G a b) x
  rw [equivariant_orbit (richardsonCellInclusion G a b) x] at h
  unfold orbitNatDim
  exact congrArg (fun d : WithBot ℕ∞ => (d.unbotD 0).toNat) h

/-- Every Richardson point has the same flag image and torus orbit dimension as a point
of an open Richardson stratum whose endpoints lie in its Bruhat interval. -/
theorem richardsonVariety_orbit_stratum (a b : G.weylGroup)
    (x : (richardsonVariety G a b).points) :
    ∃ c d : G.weylGroup, WeylBruhatLE G.rootBase a c ∧
      WeylBruhatLE G.rootBase c d ∧ WeylBruhatLE G.rootBase d b ∧
      ∃ y : (richardsonCell G c d).points,
        Variety.mapPoints (richardsonCellInclusion G c d) y =
          Variety.mapPoints (richardsonInclusion G a b) x ∧
        orbitNatDim (torusVariety G) (richardsonVariety G a b) x =
          orbitNatDim (torusVariety G) (richardsonCell G c d) y := by
  obtain ⟨c, d, hac, hcd, hdb, hx⟩ :=
    richardsonVariety_cells_cover G a b ((richardsonVariety G a b).pointMap x)
  have hp : (flagVariety G).pointMap
      (Variety.mapPoints (richardsonInclusion G a b) x) ∈
        Set.range (richardsonCellInclusion G c d).left := by
    rw [Variety.pointMap_mapPoints]
    exact hx
  obtain ⟨y, hy⟩ := Variety.exists_mapPoints_eq (richardsonCellInclusion G c d)
    (Variety.mapPoints (richardsonInclusion G a b) x) hp
  refine ⟨c, d, hac, hcd, hdb, y, hy, ?_⟩
  calc
    _ = orbitNatDim (torusVariety G) (flagVariety G)
        (Variety.mapPoints (richardsonInclusion G a b) x) :=
      (richardsonInclusion_orbitNatDim G a b x).symm
    _ = orbitNatDim (torusVariety G) (flagVariety G)
        (Variety.mapPoints (richardsonCellInclusion G c d) y) :=
      congrArg (orbitNatDim (torusVariety G) (flagVariety G)) hy.symm
    _ = _ := cell_orbit_dimension G c d y

end
end SchubertGeometry
