import OrbitComplexity.FrobeniusSplitting.Normality.FiniteCover
import OrbitComplexity.FrobeniusSplitting.Normality.ModelDiagrams
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Batteries.Tactic.Lint

/-!
# Arithmetic coordinate diagrams of affine intersections

Restriction maps on finite affine intersections define a coordinate algebra functor.
Finite-presentation structure maps yield finitely presented coordinate algebras, and
smooth intersections retain smooth arithmetic models over a common coefficient ring.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u v w

/-- The coordinates of an affine scheme of finite presentation are finitely presented. -/
private theorem coordinates_finitePresentation (K : CommRingCat.{u}) (X : Over (Spec K))
    [IsAffine X.left] [LocallyOfFinitePresentation X.hom] :
    Algebra.FinitePresentation K (((algΓ K).obj X).unop) := by
  change ((X.hom.appTop).hom.comp (Scheme.ΓSpecIso K).inv.hom).FinitePresentation
  exact X.hom.finitePresentation_appTop.comp
    (RingHom.FinitePresentation.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso K).inv))

/-- The coordinates of a smooth affine scheme are smooth. -/
private theorem coordinates_smooth (K : CommRingCat.{u}) (X : Over (Spec K))
    [IsAffine X.left] [Smooth X.hom] :
    Algebra.Smooth K (((algΓ K).obj X).unop) := by
  change ((X.hom.appTop).hom.comp (Scheme.ΓSpecIso K).inv.hom).Smooth
  exact (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso K).inv)).comp
      (HasRingHomProperty.appTop (P := @Smooth) X.hom inferInstance)

/-- Coordinate algebras and restriction maps of an open diagram over the base ring. -/
noncomputable def intersectionCoordinates {K : Type u} [kComm : CommRing K]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    {J : Type v} [jCat : Category.{w} J] (V : Jᵒᵖ ⥤ X.Opens) :
    J ⥤ CommAlgCat.{u} K :=
  ((V ⋙ X.restrictFunctor ⋙ Over.map base) ⋙ algΓ (.of K)).unop

variable {X : Scheme.{u}} {I : Type u} {K : Type u} [CommRing K]

/-- Finite-presentation structure maps give finite-presentation intersection coordinates. -/
private theorem intersectionCoordinates_finite
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (s : {s : Finset I // s.Nonempty}) :
    Algebra.FinitePresentation K ((intersectionCoordinates f (intersectionOpens U)).obj s) := by
  let D := intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map f
  have : IsAffine (D.obj (.op s)).left := intersectionOpens_affine U hU (.op s)
  have : LocallyOfFinitePresentation (D.obj (.op s)).hom := by
    change LocallyOfFinitePresentation (((intersectionOpens U).obj (.op s)).ι ≫ f)
    infer_instance
  exact coordinates_finitePresentation (.of K) (D.obj (.op s))

/-- Smooth intersection structure maps give smooth intersection coordinates. -/
private theorem intersectionCoordinates_smooth
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ Spec (.of K)) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (s : {s : Finset I // s.Nonempty})
    [Smooth (((intersectionOpens U).obj (.op s)).ι ≫ f)] :
    Algebra.Smooth K ((intersectionCoordinates f (intersectionOpens U)).obj s) := by
  let D := intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map f
  have : IsAffine (D.obj (.op s)).left := intersectionOpens_affine U hU (.op s)
  have : Smooth (D.obj (.op s)).hom := by
    change Smooth (((intersectionOpens U).obj (.op s)).ι ≫ f)
    infer_instance
  exact coordinates_smooth (.of K) (D.obj (.op s))

open scoped TensorProduct

/-- Coordinate diagrams of finite affine intersections admit arithmetic models preserving
smoothness on selected intersections and every restriction map. -/
theorem exists_intersection_models [Finite I]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (smoothNodes : Set {s : Finset I // s.Nonempty})
    (hsm : ∀ s ∈ smoothNodes, Smooth (((intersectionOpens U).obj (.op s)).ι ≫ f)) :
    ∃ (R : Subalgebra ℤ K)
      (D₀ : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
      (e : ∀ s, K ⊗[R] D₀.obj s ≃ₐ[K] (intersectionCoordinates f (intersectionOpens U)).obj s),
      R.FG ∧ (∀ s, Algebra.FinitePresentation R (D₀.obj s)) ∧
      (∀ s, s ∈ smoothNodes → Algebra.Smooth R (D₀.obj s)) ∧
      ∀ s t (g : s ⟶ t), (e t).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (D₀.map g).hom) =
        ((intersectionCoordinates f (intersectionOpens U)).map g).hom.comp (e s).toAlgHom := by
  have (s : {s : Finset I // s.Nonempty}) :
      Algebra.FinitePresentation K ((intersectionCoordinates f (intersectionOpens U)).obj s) :=
    intersectionCoordinates_finite f U hU s
  apply exists_arithmetic_functor_smooth_on (intersectionCoordinates f (intersectionOpens
    U)) smoothNodes
  intro s hs
  have : Smooth (((intersectionOpens U).obj (.op s)).ι ≫ f) := hsm s hs
  exact intersectionCoordinates_smooth f U hU s

end FrobeniusSplitting
