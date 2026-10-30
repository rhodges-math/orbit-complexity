import OrbitComplexity.GroupActions.Actions.LocallyClosed
import OrbitComplexity.GroupActions.Varieties.LocallyClosedVarieties
import OrbitComplexity.GroupActions.Varieties.Factorization

/-! # Orbits as varieties

The reduced induced structure on the locally closed scheme image of an orbit morphism is a
variety. Its dimension is the dimension assigned through the orbit's scheme closure.

## Main definitions

* `GroupActions.orbitVariety`: the reduced induced variety on a scheme orbit.
* `GroupActions.orbitInclusion`: the inclusion of the orbit variety.

## Main results

* `GroupActions.orbitVariety_dim`: the orbit variety has the orbit's dimension.
* `GroupActions.orbitVarietyIntegral`: an orbit of an irreducible group is integral.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]

omit [IsAlgClosed K] in
private theorem orbitImage_irreducible [IrreducibleSpace H.scheme] (x : X.points) :
    IsIrreducible (Set.range ((Variety.orbitMorphism H X x).left : H.scheme → X.scheme)) := by
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ H.scheme).image
      (Variety.orbitMorphism H X x).left (Variety.orbitMorphism H X x).left.continuous.continuousOn

/-- The reduced induced variety on the locally closed image of an orbit morphism. -/
def orbitVariety (x : X.points) : Variety K :=
  X.locallyClosedSubvariety (Set.range (Variety.orbitMorphism H X x).left)
    (orbitImage_locallyClosed H X x)

/-- The inclusion of the orbit variety into the ambient variety. -/
def orbitInclusion (x : X.points) : (orbitVariety H X x).toOver ⟶ X.toOver :=
  X.locallyClosedInclusion (Set.range (Variety.orbitMorphism H X x).left)
    (orbitImage_locallyClosed H X x)

/-- The orbit inclusion is a preimmersion. -/
instance orbitInclusion_isPreimmersion (x : X.points) :
    IsPreimmersion (orbitInclusion H X x).left :=
  inferInstanceAs (IsPreimmersion (X.locallyClosedInclusion
    (Set.range (Variety.orbitMorphism H X x).left) (orbitImage_locallyClosed H X x)).left)

/-- The orbit inclusion has the same image as the orbit morphism. -/
theorem orbitInclusion_range (x : X.points) :
    Set.range ((orbitInclusion H X x).left : (orbitVariety H X x).scheme → X.scheme) =
      Set.range ((Variety.orbitMorphism H X x).left : H.scheme → X.scheme) :=
  X.locallyClosedInclusion_range _ (orbitImage_locallyClosed H X x)

/-- The orbit morphism with codomain restricted to the orbit variety. -/
def orbitProjection (x : X.points) : H.toOver ⟶ (orbitVariety H X x).toOver := by
  let i := orbitInclusion H X x
  let f := Variety.orbitMorphism H X x
  have himage : Set.range (f.left : H.scheme → X.scheme) ⊆ Set.range i.left := by
    rw [show i = orbitInclusion H X x from rfl, orbitInclusion_range]
  let g : H.scheme ⟶ (orbitVariety H X x).scheme :=
    liftPreimmersion (X := X.scheme) (Y := H.scheme) i.left f.left himage
  refine Over.homMk g ?_
  change g ≫ (orbitVariety H X x).toSpec = H.toSpec
  have hi : i.left ≫ X.toSpec = (orbitVariety H X x).toSpec := i.w
  rw [← hi, ← Category.assoc]
  dsimp only [g]
  rw [liftPreimmersion_fac]
  exact f.w

/-- The projection to the orbit variety factors the original orbit morphism. -/
theorem orbitProjection_fac (x : X.points) :
    orbitProjection H X x ≫ orbitInclusion H X x = Variety.orbitMorphism H X x := by
  apply Over.OverMorphism.ext
  exact liftPreimmersion_fac (X := X.scheme) (Y := H.scheme)
    (Z := (orbitVariety H X x).scheme) _ _ (by rw [orbitInclusion_range])

/-- The projection from the acting group to its orbit variety is surjective. -/
instance orbitProjection_surjective (x : X.points) :
    Surjective (orbitProjection H X x).left := by
  constructor
  intro y
  have hy : (orbitInclusion H X x).left y ∈
      Set.range ((Variety.orbitMorphism H X x).left : H.scheme → X.scheme) := by
    rw [← orbitInclusion_range H X x]
    exact ⟨y, rfl⟩
  obtain ⟨h, hh⟩ := hy
  refine ⟨h, (orbitInclusion H X x).left.isEmbedding.injective ?_⟩
  have hcomp := congrArg Over.Hom.left (orbitProjection_fac H X x)
  exact (congrArg (fun m : H.scheme ⟶ X.scheme ↦ m h) hcomp).trans hh

/-- The projection from the acting group is also surjective on rational points. -/
theorem orbitProjection_points_surjective (x : X.points) :
    Function.Surjective (Variety.mapPoints (orbitProjection H X x)) := by
  intro y
  exact Variety.exists_mapPoints_eq _ y
    ((orbitProjection H X x).left.surjective ((orbitVariety H X x).pointMap y))

private theorem orbit_point_mem (x : X.points) (p : (orbitVariety H X x).points) :
    Variety.mapPoints (orbitInclusion H X x) p ∈ MulAction.orbit H.points x := by
  have hp : X.pointMap (Variety.mapPoints (orbitInclusion H X x) p) ∈
      Set.range ((Variety.orbitMorphism H X x).left : H.scheme → X.scheme) := by
    rw [← orbitInclusion_range H X x, Variety.pointMap_mapPoints]
    exact ⟨(orbitVariety H X x).pointMap p, rfl⟩
  obtain ⟨h, hh⟩ := Variety.exists_mapPoints_eq (Variety.orbitMorphism H X x)
    (Variety.mapPoints (orbitInclusion H X x) p) hp
  rw [← hh, Variety.mapPoints_orbitMorphism]
  exact MulAction.mem_orbit x h

/-- Rational points of the orbit variety identify with the original rational-point orbit. -/
def orbitPointsEquiv (x : X.points) :
    (orbitVariety H X x).points ≃ MulAction.orbit H.points x := by
  let F : (orbitVariety H X x).points → MulAction.orbit H.points x :=
    fun p ↦ ⟨Variety.mapPoints (orbitInclusion H X x) p, orbit_point_mem H X x p⟩
  apply Equiv.ofBijective F
  constructor
  · intro p q hpq
    exact Variety.mapPoints_injective_of_mono _ (congrArg Subtype.val hpq)
  · intro y
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp y.property
    have hmem : X.pointMap y.val ∈ Set.range ((orbitInclusion H X x).left :
        (orbitVariety H X x).scheme → X.scheme) := by
      rw [orbitInclusion_range]
      refine ⟨H.pointMap h, ?_⟩
      rw [← Variety.pointMap_mapPoints, Variety.mapPoints_orbitMorphism, hh]
    obtain ⟨p, hp⟩ := Variety.exists_mapPoints_eq (orbitInclusion H X x) y.val hmem
    exact ⟨p, Subtype.ext hp⟩

/-- The orbit variety has the topology induced on the image of the orbit morphism. -/
def orbitHomeomorph (x : X.points) : (orbitVariety H X x).scheme ≃ₜ
    Set.range ((Variety.orbitMorphism H X x).left : H.scheme → X.scheme) :=
  X.locallyClosedHomeomorph _ (orbitImage_locallyClosed H X x)

/-- The orbit of an irreducible group variety is irreducible. -/
instance orbitVarietyIrreducible [IrreducibleSpace H.scheme] (x : X.points) :
    IrreducibleSpace (orbitVariety H X x).scheme := by
  have : IrreducibleSpace
      (Set.range ((Variety.orbitMorphism H X x).left : H.scheme → X.scheme)) :=
    Subtype.irreducibleSpace (orbitImage_irreducible H X x)
  exact (orbitHomeomorph H X x).irreducibleSpace_iff.mpr inferInstance

/-- The orbit variety of an irreducible group variety is integral. -/
instance orbitVarietyIntegral [IrreducibleSpace H.scheme] (x : X.points) :
    IsIntegral (orbitVariety H X x).scheme :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The dimension of the orbit variety equals the dimension of its scheme closure. -/
theorem orbitVariety_dim [IrreducibleSpace H.scheme] (x : X.points) :
    (orbitVariety H X x).dim = orbitDim H X x := by
  have hdim := X.locallyClosedSubvariety_dim
    (Set.range (Variety.orbitMorphism H X x).left) (orbitImage_locallyClosed H X x)
    (orbitImage_irreducible H X x)
  rw [← orbitClosure_eq H X x] at hdim
  exact hdim

end

end GroupActions
