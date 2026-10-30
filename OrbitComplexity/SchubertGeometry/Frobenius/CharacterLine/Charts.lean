import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Module
import OrbitComplexity.FrobeniusSplitting.Modules.FunctionsBaseChange
import OrbitComplexity.SchubertGeometry.BSDH.Construction

/-! # torsor charts of the full-character module -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GroupActions ReductiveGroups

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Torsor-preimage functions on the flag chart are functions on the big cell. -/
def flagFunctionsChartIso (g : G.points) :
    (Scheme.Modules.restrictFunctor (flagChartMorphism G g).left).obj
        ((Scheme.Modules.pushforward (flagQuotient G)).obj
          (SheafOfModules.unit (reductiveVariety G).scheme.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward (bigCellFst G).left).obj
        (SheafOfModules.unit (bigCellVariety G).scheme.ringCatSheaf) :=
  FrobeniusSplitting.CharacterLine.openFunctionsBaseChange (bigCellFst G).left (translatedBigCell G
    g).left
    (flagChartMorphism G g).left (flagQuotient G)
    ((flagTorsorPullback G g).map (Over.forget (Spec (.of K))))

/-- The full-character sheaf on a word is pulled back along its original endpoint. -/
def wordCharacterModule (chi : G.characters) (word : List G.rootBase.support) :
    (bsdhScheme G word).Modules :=
  (Scheme.Modules.pullback (bsdhMap G word)).obj (flagCharacterModule G chi)

end SchubertGeometry.CharacterLine
