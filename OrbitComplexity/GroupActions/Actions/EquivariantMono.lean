import Batteries.Tactic.Lint
import Mathlib.CategoryTheory.Monoidal.Mod
import OrbitComplexity.GroupActions.Actions.OrbitVariety
import OrbitComplexity.GroupActions.Varieties.BijectivePoints
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Equivariant morphisms and orbit dimensions

Equivariance can be detected after a monomorphism. Equivariant morphisms induce maps
between the existing orbit varieties; injectivity on rational points preserves orbit
dimension. Proper equivariant morphisms map orbit closures onto orbit closures.
-/

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions

universe u v

section ModuleObjects

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Equivariance may be checked after an equivariant monomorphism. -/
theorem isModHom_of_comp_mono {H X Y Z : C} [MonObj H]
    [ModObj H X] [ModObj H Y] [ModObj H Z]
    (f : X ⟶ Y) (i : Y ⟶ Z) [Mono i] [IsModHom H i]
    [IsModHom H (f ≫ i)] : IsModHom H f := by
  constructor
  apply (cancel_mono i).1
  simp only [Category.assoc, IsModHom.smul_hom, MonoidalLeftAction.actionHomRight_comp]

end ModuleObjects

noncomputable section

open AlgebraicGeometry Topology

variable {K : Type u} [Field K] (H : Variety K) {X Y : Variety K}
  [GrpObj H.toOver] [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]

/-- Equivariant morphisms commute with the action on rational points. -/
theorem Variety.mapPoints_smul (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f]
    (h : H.points) (x : X.points) :
    mapPoints f (h • x) = h • mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (h • x) ≫ f =
    Y.pointsEquivOverHom (h • mapPoints f x)
  rw [pointsEquivOverHom_smul, pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom h) (X.pointsEquivOverHom x)

/-- The image of a rational-point orbit under an equivariant morphism is the target orbit. -/
theorem Variety.mapPoints_orbit (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f]
    (x : X.points) : mapPoints f '' MulAction.orbit H.points x =
      MulAction.orbit H.points (mapPoints f x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.mp hz
    rw [mapPoints_smul]
    exact MulAction.mem_orbit _ h
  · intro hy
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hy
    exact ⟨h • x, MulAction.mem_orbit _ h, (mapPoints_smul H f h x).trans hh⟩

/-- Proper equivariant morphisms map orbit closures onto the corresponding orbit closures. -/
theorem orbitClosure_image_of_proper (f : X.toOver ⟶ Y.toOver)
    [IsModHom H.toOver f] [IsProper f.left] (x : X.points) :
    f.left '' orbitClosure H X x = orbitClosure H Y (Variety.mapPoints f x) := by
  calc
    f.left '' orbitClosure H X x =
        closure (f.left '' (X.pointMap '' MulAction.orbit H.points x)) :=
      (f.left.isClosedMap.closure_image_eq_of_continuous f.left.continuous _).symm
    _ = Y.pointClosure (Variety.mapPoints f '' MulAction.orbit H.points x) := by
      simp only [Variety.pointClosure, Set.image_image, Variety.pointMap_mapPoints]
    _ = orbitClosure H Y (Variety.mapPoints f x) := by
      rw [Variety.mapPoints_orbit H f x]
      rfl

variable [IsAlgClosed K]

/-- A proper equivariant morphism maps the rational points of an orbit closure onto those of
its image orbit closure. -/
theorem orbitClosure_points_image (f : X.toOver ⟶ Y.toOver)
    [IsModHom H.toOver f] [IsProper f.left] (x : X.points) :
    Variety.mapPoints f '' {p : X.points | X.pointMap p ∈ orbitClosure H X x} =
      {q : Y.points | Y.pointMap q ∈ orbitClosure H Y (Variety.mapPoints f x)} := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    change f.left (X.pointMap p) ∈ orbitClosure H Y (Variety.mapPoints f x)
    rw [← orbitClosure_image_of_proper H f x]
    exact ⟨X.pointMap p, hp, rfl⟩
  · intro hy
    have hy' : Y.pointMap y ∈ f.left '' orbitClosure H X x := by
      rwa [orbitClosure_image_of_proper H f x]
    obtain ⟨p, hp, hpy⟩ := Variety.exists_mapPoints_eq_mem f (orbitClosure H X x)
      isClosed_closure y hy'
    exact ⟨p, hp, hpy⟩

private theorem orbitMorphism_comp (f : X.toOver ⟶ Y.toOver)
    [IsModHom H.toOver f] (x : X.points) :
    Variety.orbitMorphism H X x ≫ f =
      Variety.orbitMorphism H Y (Variety.mapPoints f x) := by
  apply Variety.mapPoints_injective
  funext h
  rw [Variety.mapPoints_comp, Variety.mapPoints_orbitMorphism,
    Variety.mapPoints_smul, Variety.mapPoints_orbitMorphism]

private theorem orbitMap_image (f : X.toOver ⟶ Y.toOver)
    [IsModHom H.toOver f] (x : X.points) :
    Set.range (((orbitInclusion H X x) ≫ f).left :
      (orbitVariety H X x).scheme → Y.scheme) ⊆
        Set.range ((orbitInclusion H Y (Variety.mapPoints f x)).left :
          (orbitVariety H Y (Variety.mapPoints f x)).scheme → Y.scheme) := by
  rintro _ ⟨p, rfl⟩
  have hp : (orbitInclusion H X x).left p ∈
      Set.range ((Variety.orbitMorphism H X x).left : H.scheme → X.scheme) := by
    rw [← orbitInclusion_range H X x]
    exact ⟨p, rfl⟩
  obtain ⟨h, hh⟩ := hp
  rw [orbitInclusion_range H Y (Variety.mapPoints f x)]
  refine ⟨h, ?_⟩
  have hc := congrArg (fun m : H.toOver ⟶ Y.toOver ↦ m.left h)
    (orbitMorphism_comp H f x)
  exact hc.symm.trans (congrArg f.left hh)

/-- The map of orbit varieties induced by an equivariant morphism. -/
def equivariantOrbitMap (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f]
    (x : X.points) : (orbitVariety H X x).toOver ⟶
      (orbitVariety H Y (Variety.mapPoints f x)).toOver := by
  let g : (orbitVariety H X x).scheme ⟶
      (orbitVariety H Y (Variety.mapPoints f x)).scheme :=
    liftPreimmersion (X := Y.scheme) (Y := (orbitVariety H X x).scheme)
      (Z := (orbitVariety H Y (Variety.mapPoints f x)).scheme)
      (orbitInclusion H Y (Variety.mapPoints f x)).left
      ((orbitInclusion H X x) ≫ f).left (orbitMap_image H f x)
  refine Over.homMk g ?_
  change g ≫ (orbitVariety H Y (Variety.mapPoints f x)).toSpec =
    (orbitVariety H X x).toSpec
  have hi : (orbitInclusion H Y (Variety.mapPoints f x)).left ≫ Y.toSpec =
      (orbitVariety H Y (Variety.mapPoints f x)).toSpec :=
    (orbitInclusion H Y (Variety.mapPoints f x)).w
  rw [← hi, ← Category.assoc]
  dsimp only [g]
  rw [liftPreimmersion_fac]
  exact ((orbitInclusion H X x) ≫ f).w

/-- The orbit map factors the ambient equivariant morphism through the target orbit. -/
@[reassoc]
theorem equivariantOrbitMap_fac (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f]
    (x : X.points) : equivariantOrbitMap H f x ≫
      orbitInclusion H Y (Variety.mapPoints f x) = orbitInclusion H X x ≫ f := by
  apply Over.OverMorphism.ext
  exact liftPreimmersion_fac (X := Y.scheme) (Y := (orbitVariety H X x).scheme)
    (Z := (orbitVariety H Y (Variety.mapPoints f x)).scheme) _ _ (orbitMap_image H f x)

private theorem orbitProjection_map (f : X.toOver ⟶ Y.toOver)
    [IsModHom H.toOver f] (x : X.points) :
    orbitProjection H X x ≫ equivariantOrbitMap H f x =
      orbitProjection H Y (Variety.mapPoints f x) := by
  have : Mono (orbitInclusion H Y (Variety.mapPoints f x)) := Over.mono_of_mono_left _
  apply (cancel_mono (orbitInclusion H Y (Variety.mapPoints f x))).mp
  rw [Category.assoc, equivariantOrbitMap_fac, ← Category.assoc, orbitProjection_fac,
    orbitProjection_fac, orbitMorphism_comp]

/-- The induced orbit map is surjective on rational points. -/
theorem equivariantOrbitMap_surjective (f : X.toOver ⟶ Y.toOver)
    [IsModHom H.toOver f] (x : X.points) :
    Function.Surjective (Variety.mapPoints (equivariantOrbitMap H f x)) := by
  intro y
  obtain ⟨h, rfl⟩ := orbitProjection_points_surjective H Y (Variety.mapPoints f x) y
  refine ⟨Variety.mapPoints (orbitProjection H X x) h, ?_⟩
  rw [← Variety.mapPoints_comp, orbitProjection_map]

/-- Injectivity of the ambient point map implies injectivity of the induced orbit map. -/
theorem equivariantOrbitMap_injective (f : X.toOver ⟶ Y.toOver)
    [IsModHom H.toOver f] (hf : Function.Injective (Variety.mapPoints f))
    (x : X.points) :
    Function.Injective (Variety.mapPoints (equivariantOrbitMap H f x)) := by
  intro a b hab
  apply Variety.mapPoints_injective_of_mono (orbitInclusion H X x)
  apply hf
  have he := congrArg (Variety.mapPoints
    (orbitInclusion H Y (Variety.mapPoints f x))) hab
  simpa only [← Variety.mapPoints_comp, equivariantOrbitMap_fac] using he

/-- An equivariant morphism injective on rational points preserves every orbit dimension. -/
theorem orbitDim_of_injective_points [IrreducibleSpace H.scheme]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f]
    (hf : Function.Injective (Variety.mapPoints f)) (x : X.points) :
    orbitDim H X x = orbitDim H Y (Variety.mapPoints f x) := by
  have hd := Variety.dim_eq_of_bijective_points (equivariantOrbitMap H f x)
    ⟨equivariantOrbitMap_injective H f hf x, equivariantOrbitMap_surjective H f x⟩
  exact (orbitVariety_dim H X x).symm.trans
    (hd.trans (orbitVariety_dim H Y (Variety.mapPoints f x)))

end

end GroupActions
