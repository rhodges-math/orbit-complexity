import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.IntersectionCovers
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateComparisons
import Mathlib.CategoryTheory.Limits.Over

/-!
# Schemes as colimits of intersection coordinate diagrams
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u

/-- An affine intersection atlas recovers a scheme as a colimit over its base. -/
theorem exists_coordinate_colimit {X : Scheme.{u}} {I K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ Spec (.of K)) (U : I → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤) :
    ∃ c : Cocone ((intersectionCoordinates f (intersectionOpens U)).op ⋙ algSpec (.of K)),
      c.pt = Over.mk f ∧ Nonempty (IsColimit c) := by
  let : Category.{u} (intersectionCover U hcover).I₀ := intersectionCoverCategory U hcover
  let : (intersectionCover U hcover).LocallyDirected := intersectionCoverDirected U hcover
  let 𝒰 := intersectionCover U hcover
  let D := intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map f
  have (s : {s : Finset I // s.Nonempty}ᵒᵖ) : IsAffine (D.obj s).left :=
    intersectionOpens_affine U hU s
  let c₀ : Cocone D :=
    { pt := Over.mk f
      ι :=
        { app := fun s ↦ Over.homMk (((intersectionOpens U).obj s).ι) rfl
          naturality := by
            intro i j g
            ext1
            change X.homOfLE (leOfHom ((intersectionOpens U).map g)) ≫
              ((intersectionOpens U).obj j).ι = ((intersectionOpens U).obj i).ι ≫ 𝟙 X
            rw [Scheme.homOfLE_ι, Category.comp_id] } }
  have h₀ : IsColimit ((Over.forget (Spec (.of K))).mapCocone c₀) := by
    exact intersectionCoverIsColimit U hcover
  have hrel : IsColimit c₀ := isColimitOfReflects (Over.forget (Spec (.of K))) h₀
  let β := coordinateDiagramIso (.of K) D
  let c := (Cocone.precompose β.inv).obj c₀
  refine ⟨c, rfl, ⟨?_⟩⟩
  exact (IsColimit.precomposeInvEquiv β _).symm hrel

end FrobeniusSplitting
