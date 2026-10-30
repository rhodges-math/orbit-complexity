import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.DeterminantSection
import OrbitComplexity.FrobeniusSplitting.Modules.OpenCoefficients
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Frames
import Batteries.Tactic.Lint
import Batteries.Tactic.OpenPrivate

/-! # The determinant section in the original character frames -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions Opposite
open CartesianMonoidalCategory MonoidalCategory
open FrobeniusSplitting.CharacterLine
open scoped CategoryTheory.MonObj

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine

open private sectionSquare from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Frames

private theorem mapped_frame_eq {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {A B C : D} {T : E}
    (s : A ⟶ B) (i : B ⟶ C) (t : A ⟶ C)
    (e : F.obj B ⟶ T) (v : F.obj C ⟶ T)
    (hs : s ≫ i = t) (he : e = F.map i ≫ v) :
    F.map s ≫ e = F.map t ≫ v := by
  rw [he, ← Category.assoc, ← F.map_comp, hs]

private theorem comp_pair_eq {D : Type*} [Category D] {A B C T E : D}
    {f : A ⟶ B} {g : B ⟶ C} {k : C ⟶ T}
    {u : A ⟶ E} {r : E ⟶ C} {v : E ⟶ T}
    (hfg : f ≫ g = u ≫ r) (hrk : r ≫ k = v) :
    f ≫ (g ≫ k) = u ≫ v := by
  rw [← Category.assoc, hfg, Category.assoc, hrk]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev U := (oppositeUnipotentVariety G).toOver

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: flagDeterminantModuleSection_chart"

/-- The determinant module section has its determinant-power coefficient in every flag chart. -/
theorem flagDeterminantModuleSection_chart (N : ℕ) (g : G.points) :
    (Scheme.Modules.restrictFunctor (flagChartMorphism G g).left).map
        (flagDeterminantModuleSection G N) ≫
        (flagCharacterChartIso G g (G.positiveRootCharacter ^ N)).hom =
      (Scheme.Modules.restrictUnitIso (flagChartMorphism G g).left).hom ≫
        Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (U G).left.ringCatSheaf)
          ((flagChartMap G g).left.appTop (DeterminantSection.positiveDetPowerFunction G N)) := by
  have hm := mapped_frame_eq
    (Scheme.Modules.restrictFunctor (flagChartMorphism G g).left)
    (flagDeterminantModuleSection G N)
    (flagCharacterInclusion G (G.positiveRootCharacter ^ N))
    (determinantCoefficientSection G N)
    (flagCharacterChartIso G g (G.positiveRootCharacter ^ N)).hom
    (flagCharacterEvaluation G g) (flagDeterminantModuleSection_inclusion G N)
    (flagCharacterChartIso_eval G g (G.positiveRootCharacter ^ N))
  have hc := openCoefficient_pullback (𝟙 (U G).left) (flagChartMap G g).left
    (flagChartMorphism G g).left (flagQuotient G) (sectionSquare G g)
    (DeterminantSection.positiveDetPowerFunction G N)
  have hi := relativeCoefficient_identity (U G).left
    ((flagChartMap G g).left.appTop (DeterminantSection.positiveDetPowerFunction G N))
  exact hm.trans (comp_pair_eq hc hi)

end SchubertGeometry.CharacterLine
