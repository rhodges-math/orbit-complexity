import OrbitComplexity.GroupActions.Varieties.Basic
import Batteries.Tactic.Lint

/-! # Morphisms and rational points of varieties

Morphisms over the base field act on rational points by composition. An isomorphism of
varieties induces a homeomorphism on their rational points.

## Main definitions

* `GroupActions.Variety.mapPoints`: the map on rational points induced by a morphism.
* `GroupActions.Variety.pointsHomeomorph`: the homeomorphism induced by an isomorphism.

## Main results

* `GroupActions.Variety.mapPoints_comp`: compatibility with composition.
* `GroupActions.Variety.continuous_mapPoints`: morphisms are continuous on rational points.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] {X Y Z : GroupActions.Variety K}

/-- Rational points identify with morphisms from the base object in the category over the field. -/
def pointsEquivOverHom (X : GroupActions.Variety K) :
    X.points ≃ (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X.toOver) where
  toFun x := Over.homMk x.val x.property
  invFun x := ⟨x.left, x.w⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Over.OverMorphism.ext rfl

/-- Composition with a morphism over the field maps rational points to rational points. -/
def mapPoints (f : X.toOver ⟶ Y.toOver) (x : X.points) : Y.points :=
  ⟨x.val ≫ f.left, by
    calc
      (x.val ≫ f.left) ≫ Y.toSpec = x.val ≫ (f.left ≫ Y.toSpec) := Category.assoc _ _ _
      _ = x.val ≫ X.toSpec := congrArg (fun m ↦ x.val ≫ m) f.w
      _ = 𝟙 _ := x.property⟩

/-- The underlying image of a rational point commutes with a morphism of varieties. -/
theorem pointMap_mapPoints (f : X.toOver ⟶ Y.toOver) (x : X.points) :
    Y.pointMap (mapPoints f x) = f.left (X.pointMap x) := rfl

/-- A morphism of varieties is continuous on rational points. -/
theorem continuous_mapPoints (f : X.toOver ⟶ Y.toOver) : Continuous (mapPoints f) := by
  apply continuous_induced_rng.mpr
  exact f.left.continuous.comp X.continuous_pointMap

/-- The identity morphism induces the identity map on rational points. -/
theorem mapPoints_id (x : X.points) : mapPoints (𝟙 X.toOver) x = x := by
  apply Subtype.ext
  exact Category.comp_id _

/-- Composition of morphisms induces composition of maps on rational points. -/
theorem mapPoints_comp (f : X.toOver ⟶ Y.toOver) (g : Y.toOver ⟶ Z.toOver)
    (x : X.points) : mapPoints (f ≫ g) x = mapPoints g (mapPoints f x) := by
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

/-- A monomorphism on schemes induces an injective map on rational points. -/
theorem mapPoints_injective_of_mono (f : X.toOver ⟶ Y.toOver) [Mono f.left] :
    Function.Injective (mapPoints f) := by
  intro x y h
  apply Subtype.ext
  exact (cancel_mono f.left).mp (congrArg Subtype.val h)

/-- An isomorphism of varieties induces a homeomorphism on their rational points. -/
def pointsHomeomorph (e : X.toOver ≅ Y.toOver) : X.points ≃ₜ Y.points where
  toFun := mapPoints e.hom
  invFun := mapPoints e.inv
  left_inv x := by
    rw [← mapPoints_comp, e.hom_inv_id, mapPoints_id]
  right_inv x := by
    rw [← mapPoints_comp, e.inv_hom_id, mapPoints_id]
  continuous_toFun := continuous_mapPoints e.hom
  continuous_invFun := continuous_mapPoints e.inv

/-- Over an algebraically closed field a variety morphism is determined by its rational points. -/
theorem mapPoints_injective [IsAlgClosed K] :
    Function.Injective (mapPoints (X := X) (Y := Y)) := by
  intro f g h
  have hf : f.left ≫ Y.toSpec = X.toSpec := f.w
  have : LocallyOfFiniteType (f.left ≫ Y.toSpec) := hf.symm ▸ X.locallyOfFiniteType
  apply Over.OverMorphism.ext
  refine AlgebraicGeometry.ext_of_apply_eq (X := X.scheme) (Y := Y.scheme) Y.toSpec
    Set.univ isClosed_univ.isLocallyClosed dense_univ ?_ ?_
  · intro x _ hx
    obtain ⟨p, hp⟩ := X.pointsEquivClosedPoints.surjective ⟨x, hx⟩
    have hp' : X.pointMap p = x := congrArg Subtype.val hp
    have heval := congrArg (fun q ↦ Y.pointMap (q p)) h
    simpa only [pointMap_mapPoints, hp'] using heval
  · exact f.w.trans g.w.symm

/-- A rational point in the image of a closed subset has a rational preimage in that subset. -/
theorem exists_mapPoints_eq_mem [IsAlgClosed K] (f : X.toOver ⟶ Y.toOver)
    (Z : Set X.scheme) (hZ : IsClosed Z) (y : Y.points)
    (hy : Y.pointMap y ∈ f.left '' Z) :
    ∃ x : X.points, X.pointMap x ∈ Z ∧ mapPoints f x = y := by
  have : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  let g : X.scheme → Y.scheme := f.left
  have hg : Continuous g := f.left.continuous
  let F : Set X.scheme := g ⁻¹' {Y.pointMap y} ∩ Z
  have hF : IsClosed F := ((Y.pointsEquivClosedPoints y).property.preimage hg).inter hZ
  have hne : F.Nonempty := by
    obtain ⟨x, hxZ, hx⟩ := hy
    exact ⟨x, hx, hxZ⟩
  obtain ⟨x, hxF, hxc⟩ := nonempty_inter_closedPoints hne hF.isLocallyClosed
  obtain ⟨p, hp⟩ := X.pointsEquivClosedPoints.surjective ⟨x, hxc⟩
  have hp' : X.pointMap p = x := congrArg Subtype.val hp
  refine ⟨p, ?_, Y.pointMap_injective ?_⟩
  · exact hp'.symm ▸ hxF.2
  · rw [pointMap_mapPoints, hp']
    exact hxF.1

/-- A rational point in the scheme image of a variety morphism has a rational preimage. -/
theorem exists_mapPoints_eq [IsAlgClosed K] (f : X.toOver ⟶ Y.toOver) (y : Y.points)
    (hy : Y.pointMap y ∈ Set.range (f.left : X.scheme → Y.scheme)) :
    ∃ x : X.points, mapPoints f x = y := by
  obtain ⟨x, _, hx⟩ := exists_mapPoints_eq_mem f Set.univ isClosed_univ y
    (by simpa only [Set.image_univ] using hy)
  exact ⟨x, hx⟩

end

end GroupActions.Variety
