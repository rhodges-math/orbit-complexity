import OrbitComplexity.Paper.Deodhar.ComponentOrbitDimensions
import OrbitComplexity.SchubertGeometry.Cells.RichardsonActions
import OrbitComplexity.SchubertGeometry.Deodhar.ComponentRichardson

/-! # Intrinsic components inside Richardson strata

The final opposite-cell condition and the ambient ordinary cell place an intrinsic component
inside its open Richardson stratum. The reduced induced structures give a regular equivariant
immersion preserving the torus orbits and their dimensions.
-/

open CategoryTheory AlgebraicGeometry Topology ReductiveGroups SchubertGeometry GroupActions
namespace SchubertOrbits

export SchubertGeometry (deodharRichardsonMap deodharRichardsonMap_comp
  deodharRichardsonMap_isImmersion deodharRichardsonMap_comp_assoc)
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : BruhatIntervals.Subexpression word)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)

private theorem equivariant_of_comp {C : Type*} [Category C]
    [CartesianMonoidalCategory C] (H X Y Z : C) [MonObj H]
    [ModObj H X] [ModObj H Y] [ModObj H Z]
    (f : X ⟶ Y) (i : Y ⟶ Z) (j : X ⟶ Z) [Mono i]
    [IsModHom H i] [IsModHom H j] (h : f ≫ i = j) : IsModHom H f := by
  constructor
  apply (cancel_mono i).mp
  rw [Category.assoc, h, IsModHom.smul_hom]
  rw [Category.assoc, IsModHom.smul_hom, ← Category.assoc,
    ← MonoidalCategory.MonoidalLeftAction.actionHomRight_comp, h]

/-- The intrinsic component map into its Richardson stratum is torus equivariant. -/
instance deodharRichardsonMap_torus :
    IsModHom (torusVariety G).toOver (deodharRichardsonMap G expression hred) := by
  let i := richardsonCellInclusion G
    (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length)
    (simpleWeylWord G.rootBase word)
  have : Mono i := Over.mono_of_mono_left i
  exact equivariant_of_comp (torusVariety G).toOver _ _ _
    (deodharRichardsonMap G expression hred) i (deodharInclusion G expression hred)
    (deodharRichardsonMap_comp G expression hred)

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

/-- The Richardson stratum and its intrinsic component assign the same dimension to an orbit. -/
theorem deodharRichardsonMap_orbitNatDim
    (x : (deodharComponent G expression hred).points) :
    orbitNatDim (torusVariety G)
      (richardsonCell G (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length)
        (simpleWeylWord G.rootBase word))
      (Variety.mapPoints (deodharRichardsonMap G expression hred) x) =
        orbitNatDim (torusVariety G) (deodharComponent G expression hred) x := by
  have h := orbit_image_dim (torusVariety G) (deodharComponent G expression hred)
    (richardsonCell G (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length)
      (simpleWeylWord G.rootBase word)) (deodharRichardsonMap G expression hred) x
  rw [equivariant_orbit (H := torusVariety G)
    (X := deodharComponent G expression hred)
    (Y := richardsonCell G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length)
      (simpleWeylWord G.rootBase word)) (deodharRichardsonMap G expression hred) x] at h
  unfold orbitNatDim
  exact congrArg (fun d : WithBot ℕ∞ => (d.unbotD 0).toNat) h

end
end SchubertOrbits
