import OrbitComplexity.GroupActions.Varieties.Reduced.Retracts
import OrbitComplexity.GroupActions.Actions.Intersections
import OrbitComplexity.GroupActions.Rosenlicht.IntegralProducts
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-! # Reducedness of equivariant intersections -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace GroupActions

/-- A smooth transverse action makes the intersection of two equivariant reduced
subschemes reduced whenever their product is reduced and locally noetherian. -/
theorem reduced_equivariant_intersection {S : Scheme.{u}}
    (B O F X Y : Over S) [GrpObj B] [GrpObj O]
    [ModObj B F] [ModObj O F] [ModObj B X] [ModObj O Y]
    (f : X ⟶ F) (g : Y ⟶ F) [IsModHom B f] [IsModHom O g]
    [Smooth (transverseAction B O F).left]
    [IsReduced (X ⊗ Y).left] [IsLocallyNoetherian (X ⊗ Y).left] :
    IsReduced (pullback f g).left := by
  let p := transverseAction B O F
  let k := f ⊗ₘ g
  have hraw : IsReduced (pullback p.left k.left) := inferInstance
  have : IsReduced (pullback p k).left := by
    let c := PreservesPullback.iso (Over.forget S) p k
    have : IsReduced (pullback ((Over.forget S).map p) ((Over.forget S).map k)) := hraw
    exact isReduced_of_isOpenImmersion c.hom
  let e := equivariantIntersectionIso B O F f g
  have : IsReduced (((B ⊗ O) ⊗ pullback f g).left) :=
    isReduced_of_isOpenImmersion e.hom.left
  let Z := pullback f g
  let H := B ⊗ O
  let s : Z ⟶ H ⊗ Z := lift (1 : Z ⟶ H) (𝟙 Z)
  let r : H ⊗ Z ⟶ Z := snd H Z
  have hsr : s ≫ r = 𝟙 Z := lift_snd _ _
  exact reduced_of_retraction s.left r.left
    (congrArg (fun a : Z ⟶ Z => a.left) hsr)

end GroupActions
