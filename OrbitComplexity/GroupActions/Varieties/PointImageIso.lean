import OrbitComplexity.GroupActions.Varieties.Factorization
import OrbitComplexity.GroupActions.Varieties.Noetherian
import OrbitComplexity.GroupActions.Varieties.ClosedPoints
import OrbitComplexity.GroupActions.Varieties.OpenPoints

/-! # Isomorphisms determined by rational images

Over an algebraically closed field, constructibility makes the scheme image of a variety
morphism determined by its rational image. Reduced preimmersions with the same image
factor uniquely through each other and give an isomorphism over the ambient variety.

## Main results

* `GroupActions.Variety.range_subset_of_mapPoints`: rational image containment detects scheme
  image containment.

## Main definitions

* `GroupActions.Variety.pointImageIso`: the isomorphism between equal reduced images.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y Z : GroupActions.Variety K}

/-- Inclusion of rational images implies inclusion of scheme images for variety morphisms. -/
theorem range_subset_of_mapPoints {A B C : GroupActions.Variety K}
    (f : A.toOver ⟶ C.toOver) (i : B.toOver ⟶ C.toOver)
    (h : Set.range (mapPoints f) ⊆ Set.range (mapPoints i)) :
    Set.range (f.left : A.scheme → C.scheme) ⊆ Set.range (i.left : B.scheme → C.scheme) := by
  have : JacobsonSpace C.scheme := LocallyOfFiniteType.jacobsonSpace C.toSpec
  intro z hz
  by_contra hzi
  obtain ⟨p, ⟨hp, hpi⟩, hpc⟩ := GroupActions.constructible_closedPoint (X := C.scheme)
    ((isConstructible_range f).sdiff (isConstructible_range i)) ⟨z, hz, hzi⟩
  obtain ⟨q, hq⟩ := C.pointsEquivClosedPoints.surjective ⟨p, hpc⟩
  have hqp : C.pointMap q = p := congrArg Subtype.val hq
  obtain ⟨a, ha⟩ := exists_mapPoints_eq f q (by rw [hqp]; exact hp)
  obtain ⟨b, hb⟩ := h ⟨a, ha⟩
  apply hpi
  refine ⟨B.pointMap b, ?_⟩
  change C.pointMap (mapPoints i b) = p
  rw [hb, hqp]

/-- Equality of rational images implies equality of scheme images for variety morphisms. -/
theorem range_eq_of_mapPoints (f : X.toOver ⟶ Z.toOver) (g : Y.toOver ⟶ Z.toOver)
    (hp : Set.range (mapPoints f) = Set.range (mapPoints g)) :
    Set.range (f.left : X.scheme → Z.scheme) = Set.range (g.left : Y.scheme → Z.scheme) := by
  exact Set.Subset.antisymm (range_subset_of_mapPoints f g hp.le)
    (range_subset_of_mapPoints g f hp.ge)

/-- Reduced preimmersions with equal rational images are isomorphic over their ambient variety. -/
def pointImageIso (f : X.toOver ⟶ Z.toOver) (g : Y.toOver ⟶ Z.toOver)
    [IsPreimmersion f.left] [IsPreimmersion g.left]
    (hp : Set.range (mapPoints f) = Set.range (mapPoints g)) : X.toOver ≅ Y.toOver := by
  let f₀ : X.scheme ⟶ Z.scheme := f.left
  let g₀ : Y.scheme ⟶ Z.scheme := g.left
  have hrange : Set.range f₀ = Set.range g₀ := range_eq_of_mapPoints f g hp
  let k₀ : X.scheme ⟶ Y.scheme :=
    GroupActions.liftPreimmersion g₀ f₀ hrange.le
  let l₀ : Y.scheme ⟶ X.scheme :=
    GroupActions.liftPreimmersion f₀ g₀ hrange.ge
  have hk₀ : k₀ ≫ g₀ = f₀ := GroupActions.liftPreimmersion_fac g₀ f₀ hrange.le
  have hl₀ : l₀ ≫ f₀ = g₀ := GroupActions.liftPreimmersion_fac f₀ g₀ hrange.ge
  let k : X.toOver ⟶ Y.toOver := Over.homMk k₀ (by
    change k₀ ≫ Y.toSpec = X.toSpec
    rw [← (show g₀ ≫ Z.toSpec = Y.toSpec from g.w), ← Category.assoc, hk₀]
    exact f.w)
  let l : Y.toOver ⟶ X.toOver := Over.homMk l₀ (by
    change l₀ ≫ X.toSpec = Y.toSpec
    rw [← (show f₀ ≫ Z.toSpec = X.toSpec from f.w), ← Category.assoc, hl₀]
    exact g.w)
  have hk : k ≫ g = f := by
    apply Over.OverMorphism.ext
    exact hk₀
  have hl : l ≫ f = g := by
    apply Over.OverMorphism.ext
    exact hl₀
  have : Mono f := Over.mono_of_mono_left f
  have : Mono g := Over.mono_of_mono_left g
  exact
    { hom := k
      inv := l
      hom_inv_id := (cancel_mono f).mp (by simp only [Category.assoc, hl, hk, Category.id_comp])
      inv_hom_id := (cancel_mono g).mp (by simp only [Category.assoc, hk, hl, Category.id_comp]) }

/-- The image isomorphism commutes with the two ambient morphisms. -/
@[reassoc]
theorem pointImageIso_hom_comp (f : X.toOver ⟶ Z.toOver) (g : Y.toOver ⟶ Z.toOver)
    [IsPreimmersion f.left] [IsPreimmersion g.left]
    (hp : Set.range (mapPoints f) = Set.range (mapPoints g)) :
    (pointImageIso f g hp).hom ≫ g = f := by
  apply Over.OverMorphism.ext
  let f₀ : X.scheme ⟶ Z.scheme := f.left
  let g₀ : Y.scheme ⟶ Z.scheme := g.left
  have hrange : Set.range f₀ = Set.range g₀ := range_eq_of_mapPoints f g hp
  change GroupActions.liftPreimmersion g₀ f₀ hrange.le ≫ g₀ = f₀
  exact GroupActions.liftPreimmersion_fac g₀ f₀ hrange.le

/-- The inverse image isomorphism also commutes with the ambient morphisms. -/
@[reassoc]
theorem pointImageIso_inv_comp (f : X.toOver ⟶ Z.toOver) (g : Y.toOver ⟶ Z.toOver)
    [IsPreimmersion f.left] [IsPreimmersion g.left]
    (hp : Set.range (mapPoints f) = Set.range (mapPoints g)) :
    (pointImageIso f g hp).inv ≫ f = g := by
  calc
    _ = (pointImageIso f g hp).inv ≫ ((pointImageIso f g hp).hom ≫ g) :=
      congrArg (fun t ↦ (pointImageIso f g hp).inv ≫ t) (pointImageIso_hom_comp f g hp).symm
    _ = _ := by simp

end

end GroupActions.Variety
