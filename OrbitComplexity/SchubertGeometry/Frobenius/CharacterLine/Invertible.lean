import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Trivialization
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Charts
import TauCeti.AlgebraicGeometry.LineBundle.Pullback
import Batteries.Tactic.Lint

set_option autoImplicit false

/-! # The full-character line on the flag variety and the BSDH word -/

open AlgebraicGeometry CategoryTheory ReductiveGroups GroupActions

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def rangeTrivialization (g : G.points) (chi : G.characters) :
    (flagCharacterModule G chi).restrict (flagChartMorphism G g).left.opensRange.ι ≅
      SheafOfModules.unit (flagChartMorphism G g).left.opensRange.toScheme.ringCatSheaf := by
  let j := (flagChartMorphism G g).left
  let e := j.isoOpensRange
  exact ((Scheme.Modules.restrictFunctorCongr j.isoOpensRange_inv_comp).symm.app
      (flagCharacterModule G chi)) ≪≫
    (Scheme.Modules.restrictFunctorComp e.inv j).app (flagCharacterModule G chi) ≪≫
    (Scheme.Modules.restrictFunctor e.inv).mapIso (flagCharacterChartIso G g chi) ≪≫
    Scheme.Modules.restrictUnitIso e.inv

/-- The original full-character equalizer is an invertible sheaf on the flag variety. -/
instance flagCharacterModule_invertible (chi : G.characters) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (flagVariety G).scheme (flagCharacterModule G chi) := by
  apply TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mpr
  refine ⟨G.points, fun g => (flagChartMorphism G g).left.opensRange, ?_,
    fun g => ⟨(rangeTrivialization G g chi).symm⟩⟩
  change TopologicalSpace.IsOpenCover fun g => ((flagSchemeCover G).f g).opensRange
  exact (flagSchemeCover G).isOpenCover_opensRange

/-- The character module on the BSDH word is invertible by its endpoint pullback. -/
instance wordCharacterModule_invertible (chi : G.characters) (word : List G.rootBase.support) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      (bsdhScheme G word) (wordCharacterModule G chi word) := by
  unfold wordCharacterModule
  infer_instance

end SchubertGeometry.CharacterLine
