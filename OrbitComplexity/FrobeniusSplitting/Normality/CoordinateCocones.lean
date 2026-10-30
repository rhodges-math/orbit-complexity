import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.IntersectionMaps
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateColimits

/-!
# Canonical cocones of affine intersection coordinates
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u

@[implicit_reducible]
private noncomputable def intersectionSchemeCocone {X : Scheme.{u}} {I K : Type u} [CommRing K]
    (f : X ⟶ Spec (.of K)) (U : I → X.Opens) :
    Cocone (intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map f) where
  pt := Over.mk f
  ι :=
    { app := fun s ↦ Over.homMk (((intersectionOpens U).obj s).ι) rfl
      naturality := by
        intro i j g
        ext1
        change X.homOfLE (leOfHom ((intersectionOpens U).map g)) ≫
          ((intersectionOpens U).obj j).ι = ((intersectionOpens U).obj i).ι ≫ 𝟙 X
        rw [Scheme.homOfLE_ι, Category.comp_id] }

/-- The coordinate spectra of affine intersections have a canonical cocone in their scheme. -/
@[implicit_reducible]
noncomputable def intersectionCoordinateCocone {X : Scheme.{u}} {I K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ Spec (.of K)) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    Cocone ((intersectionCoordinates f (intersectionOpens U)).op ⋙ algSpec (.of K)) := by
  let E := intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map f
  have (s : {s : Finset I // s.Nonempty}ᵒᵖ) : IsAffine (E.obj s).left :=
    intersectionOpens_affine U hU s
  exact (Cocone.precompose (coordinateDiagramIso (.of K) E).inv).obj
    (intersectionSchemeCocone f U)

/-- The canonical coordinate cocone of an affine open cover is a colimit. -/
noncomputable def coordinateCoconeIsColimit {X : Scheme.{u}} {I K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ Spec (.of K)) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤) :
    IsColimit (intersectionCoordinateCocone f U hU) := by
  letI := intersectionCoverDirected U hcover
  let E := intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map f
  have (s : {s : Finset I // s.Nonempty}ᵒᵖ) : IsAffine (E.obj s).left :=
    intersectionOpens_affine U hU s
  have h₀ : IsColimit
      ((Over.forget (Spec (.of K))).mapCocone (intersectionSchemeCocone f U)) :=
    intersectionCoverIsColimit U hcover
  have hrel : IsColimit (intersectionSchemeCocone f U) :=
    isColimitOfReflects (Over.forget (Spec (.of K))) h₀
  exact (IsColimit.precomposeInvEquiv (coordinateDiagramIso (.of K) E) _).symm hrel

/-- Coordinate cocones commute with a morphism carrying each chart into its labeled chart. -/
theorem coordinateCocone_map {X Y : Scheme.{u}} {I J K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of K))
    (U : J → X.Opens) (V : I → Y.Opens)
    (hU : ∀ j, IsAffineOpen (U j)) (hV : ∀ i, IsAffineOpen (V i))
    (label : J → I) (hle : ∀ j, U j ≤ f ⁻¹ᵁ V (label j))
    (s : {s : Finset J // s.Nonempty}ᵒᵖ) :
    (intersectionCoordinateCocone (f ≫ g) U hU).ι.app s ≫
      (Over.homMk f rfl : Over.mk (f ≫ g) ⟶ Over.mk g) =
      (algSpec (.of K)).map ((intersectionCoordinateMap f g U V label hle).app s.unop).op ≫
        (intersectionCoordinateCocone g V hV).ι.app ((intersectionIndexMap label).op.obj s) := by
  let EX := intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map (f ≫ g)
  let EY := intersectionOpens V ⋙ Y.restrictFunctor ⋙ Over.map g
  have (s : {s : Finset J // s.Nonempty}ᵒᵖ) : IsAffine (EX.obj s).left :=
    intersectionOpens_affine U hU s
  have (s : {s : Finset I // s.Nonempty}ᵒᵖ) : IsAffine (EY.obj s).left :=
    intersectionOpens_affine V hV s
  let βX := coordinateDiagramIso (.of K) EX
  let βY := coordinateDiagramIso (.of K) EY
  let t := (intersectionIndexMap label).op.obj s
  let a := (intersectionSchemeMap f g U V label hle).app s
  let eX : ((intersectionOpens U).obj s).toScheme ≅
      ((algSpec (.of K)).obj (.op ((intersectionCoordinates (f ≫ g) (intersectionOpens
        U)).obj s.unop))).left :=
    (Over.forget (Spec (.of K))).mapIso (βX.app s)
  let eY : ((intersectionOpens V).obj t).toScheme ≅
      ((algSpec (.of K)).obj (.op ((intersectionCoordinates g (intersectionOpens V)).obj
        ((intersectionIndexMap label).obj s.unop)))).left :=
    (Over.forget (Spec (.of K))).mapIso (βY.app t)
  let m := (algSpec (.of K)).map
    ((intersectionCoordinateMap f g U V label hle).app s.unop).op
  let aS : ((intersectionOpens U).obj s).toScheme ⟶ ((intersectionOpens V).obj t).toScheme :=
    f.resLE _ _ (intersection_preimage_le f U V label hle s)
  have hnat : eX.hom ≫ m.left = aS ≫ eY.hom :=
    congrArg (fun q ↦ q.left) ((algΓAlgSpecAdjunction (.of K)).unit.naturality a).symm
  ext1
  apply (cancel_epi eX.hom).mp
  change eX.hom ≫ ((eX.inv ≫ ((intersectionOpens U).obj s).ι) ≫ f) =
    eX.hom ≫ (m.left ≫ (eY.inv ≫ ((intersectionOpens V).obj t).ι))
  calc
    _ = ((intersectionOpens U).obj s).ι ≫ f := by
      simp only [← Category.assoc, eX.hom_inv_id, Category.id_comp]
    _ = aS ≫ ((intersectionOpens V).obj t).ι := by
      exact (Scheme.Hom.resLE_comp_ι f
        (intersection_preimage_le f U V label hle s)).symm
    _ = (aS ≫ eY.hom) ≫ (eY.inv ≫ ((intersectionOpens V).obj t).ι) := by
      simp only [Category.assoc, eY.hom_inv_id_assoc]
    _ = (eX.hom ≫ m.left) ≫ (eY.inv ≫ ((intersectionOpens V).obj t).ι) := by rw [hnat]
    _ = _ := by rw [Category.assoc]

end FrobeniusSplitting
