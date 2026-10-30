import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Affine refinements of flag-chart inverse images -/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting

namespace SchubertGeometry.RetainedCharacter

open private preimageSnd preimageLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage

/-- An affine refinement of a matching chart and a flag-chart inverse image. -/
structure WordPreimageRefinement {K : Type u}
    [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (cF : Cocone (F.op ⋙ algSpec (.of K)))
    (word : List G.rootBase.support) (q : cF.pt.left ⟶ bsdhScheme G word)
    (i : G.rootBase.support) where
  /-- The affine coordinate algebra of the refinement. -/
  ring : CommAlgCat.{u} K
  /-- The finite chart index in the original matching diagram. -/
  index : {s : Finset J // s.Nonempty}
  /-- A matching-frame index contained in the chart. -/
  entry : J
  /-- The frame is defined on the chosen chart. -/
  mem : entry ∈ index.val
  /-- The map to the original matching chart over the ground field. -/
  toChart : (algSpec (.of K)).obj (op ring) ⟶ (algSpec (.of K)).obj (op (F.obj index))
  /-- The map to the entire inverse image of the flag chart. -/
  toPreimage : Spec (.of ring) ⟶ wordChartPreimage G word q i
  /-- Both maps induce the same map to the original word model. -/
  triangle : toChart.left ≫ (cF.ι.app (op index)).left =
    toPreimage ≫ preimageSnd G word q i
  /-- The original structural map of the flag-chart inverse image. -/
  preimageBase : wordChartPreimage G word q i ⟶ Spec (.of K)
  /-- The canonical opposite-unipotent lift lies over that structural map. -/
  lift_over : preimageLift G word q i ≫ (oppositeUnipotentVariety G).toOver.hom =
    preimageBase
  /-- The refinement map respects the ground-field structure. -/
  base : toPreimage ≫ preimageBase =
    ((algSpec (.of K)).obj (op ring)).hom

end SchubertGeometry.RetainedCharacter
