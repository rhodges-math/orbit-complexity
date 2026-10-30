import OrbitComplexity.GroupActions.Complexity.OrbitCodimension

/-! # Orbits under equivariant isomorphisms

An equivariant variety isomorphism identifies rational-point orbits and their scheme
closures. It preserves orbit dimensions, integer codimensions, and minimum codimension.

## Main definitions

* `GroupActions.orbitQuotientEquiv`: the equivalence of orbit quotient types.

## Main results

* `GroupActions.orbitDim_iso`: orbit dimension is preserved.
* `GroupActions.orbitCodim_iso`: integer orbit codimension is preserved.
* `GroupActions.minOrbitCodim_iso`: minimum orbit codimension is preserved.
-/

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] (H : Variety K) {X Y : Variety K}
  [GrpObj H.toOver] [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
  (e : X.toOver ≅ Y.toOver) [IsModHom H.toOver e.hom]

private theorem equivariant_smul (h : H.points) (x : X.points) :
    Variety.mapPoints e.hom (h • x) = h • Variety.mapPoints e.hom x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (h • x) ≫ e.hom =
    Y.pointsEquivOverHom (h • Variety.mapPoints e.hom x)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul e.hom (H.pointsEquivOverHom h) (X.pointsEquivOverHom x)

private theorem orbitRel_iso (a b : X.points) :
    MulAction.orbitRel H.points X.points a b ↔
      MulAction.orbitRel H.points Y.points
        (Variety.mapPoints e.hom a) (Variety.mapPoints e.hom b) := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, (equivariant_smul H e h b).symm⟩
  · rintro ⟨h, hh⟩
    refine ⟨h, (Variety.pointsHomeomorph e).injective ?_⟩
    exact (equivariant_smul H e h b).trans hh

/-- An equivariant variety isomorphism identifies the types of rational-point orbits. -/
def orbitQuotientEquiv :
    MulAction.orbitRel.Quotient H.points X.points ≃
      MulAction.orbitRel.Quotient H.points Y.points :=
  Quotient.congr (Variety.pointsHomeomorph e).toEquiv (orbitRel_iso H e)

private theorem orbit_image (x : X.points) :
    Variety.mapPoints e.hom '' MulAction.orbit H.points x =
      MulAction.orbit H.points (Variety.mapPoints e.hom x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.mp hz
    rw [equivariant_smul]
    exact MulAction.mem_orbit _ h
  · intro hy
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hy
    exact ⟨h • x, MulAction.mem_orbit _ h, (equivariant_smul H e h x).trans hh⟩

/-- Equivariant isomorphisms preserve the dimension of every orbit. -/
theorem orbitDim_iso (x : X.points) :
    orbitDim H Y (Variety.mapPoints e.hom x) = orbitDim H X x := by
  rw [orbitDim, ← orbit_image H e x, Variety.subsetDim, X.pointClosure_image e]
  let h := ((Over.forget _).mapIso e).hom.homeomorph
  have hh := (h.image (X.pointClosure (MulAction.orbit H.points x))).isHomeomorph
  exact hh.topologicalKrullDim_eq.symm

/-- Equivariant isomorphisms preserve the natural dimension of every orbit. -/
theorem orbitNatDim_iso (x : X.points) :
    orbitNatDim H Y (Variety.mapPoints e.hom x) = orbitNatDim H X x := by
  unfold orbitNatDim
  rw [orbitDim_iso H e]

private theorem natDim_iso (e : X.toOver ≅ Y.toOver) : Y.natDim = X.natDim := by
  unfold Variety.natDim
  rw [← X.dim_eq_of_iso e]

/-- Equivariant isomorphisms preserve integer orbit codimension. -/
theorem orbitCodim_iso (x : X.points) :
    orbitCodim H Y (Variety.mapPoints e.hom x) = orbitCodim H X x := by
  unfold orbitCodim
  rw [natDim_iso e, orbitNatDim_iso H e]

/-- Equivariant isomorphisms preserve minimum orbit codimension. -/
theorem minOrbitCodim_iso (e : X.toOver ≅ Y.toOver) [IsModHom H.toOver e.hom] :
    minOrbitCodim H Y = minOrbitCodim H X := by
  unfold minOrbitCodim
  congr 1
  ext n
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := (Variety.pointsHomeomorph e).surjective y
    exact ⟨x, congrArg Int.toNat (orbitCodim_iso H e x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨Variety.mapPoints e.hom x, congrArg Int.toNat (orbitCodim_iso H e x)⟩

end

end GroupActions
