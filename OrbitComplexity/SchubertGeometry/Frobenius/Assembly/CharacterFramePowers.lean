import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.LiftEvaluation
import OrbitComplexity.SchubertGeometry.Normality.BottSamelson.CharacterCoefficients
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # One Borel factor for all character coframe powers

The chosen flag torsor chart constructs the Borel factor of an affine regular
lift. The same factor determines every power of the full positive-root
character in the change of line coframe.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine

open private torsor_factor
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.LiftEvaluation
open private section_character_power
  from OrbitComplexity.SchubertGeometry.Normality.BottSamelson.CharacterCoefficients

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (A : CommAlgCat.{u} K) (g : G.points)
    (a : (algSpec (.of K)).obj (.op A) ⟶ (oppositeUnipotentVariety G).toOver)
    (k : (algSpec (.of K)).obj (.op A) ⟶ (reductiveVariety G).toOver)
    (h : a ≫ flagChartMorphism G g = k ≫ flagQuotientMorphism G)

/-- The specified torsor chart constructs the Borel coordinate of a regular lift. -/
def frameBorelFactor :
    (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver :=
  (pullback.lift a k h ≫ (flagTorsorIso G g).inv) ≫
    snd (oppositeUnipotentVariety G).toOver (borelVariety G).toOver

/-- The constructed Borel coordinate factors the lift through its endpoint frame. -/
theorem frameBorelFactor_mul :
    k = (a ≫ flagChartMap G g) * (frameBorelFactor G A g a k h ≫ borelInclusion G) :=
  torsor_factor (flagChartMorphism G g) (flagQuotientMorphism G)
    (flagChartMap G g) (borelInclusion G) (flagTorsorIso G g)
    (flagTorsorIso_fst G g) (flagTorsorIso_group G g) a k h

include h in
private theorem canonical_quotient :
    (a ≫ flagChartMap G g).left ≫ flagQuotient G = k.left ≫ flagQuotient G := by
  have hcanonical : (a ≫ flagChartMap G g) ≫ flagQuotientMorphism G =
      k ≫ flagQuotientMorphism G :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t => a ≫ t) (flagChartMap_quotient G g)).trans h)
  exact congrArg (fun t => t.left) hcanonical

/-- Every character power uses the same constructed Borel unit in the
comparison between the regular lift and the chosen endpoint coframe. -/
theorem characterFrame_power (n : ℕ) :
    characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        ((algSpec (.of K)).obj (.op A)) (k.left ≫ flagQuotient G) k rfl =
      characterFrameEvaluation G (G.positiveRootCharacter ^ n)
          ((algSpec (.of K)).obj (.op A)) (k.left ≫ flagQuotient G)
          (a ≫ flagChartMap G g) (canonical_quotient G A g a k h) ≫
        Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
          ((Scheme.ΓSpecIso (.of A)).inv
            ((ProjectiveLine.positiveBorelSection G A (frameBorelFactor G A g a k h) : A) ^ n)) :=
                by
  have hrule := characterFrameEvaluation_rule G (G.positiveRootCharacter ^ n)
    ((algSpec (.of K)).obj (.op A)) (k.left ≫ flagQuotient G) k
    (a ≫ flagChartMap G g) (frameBorelFactor G A g a k h)
    rfl (canonical_quotient G A g a k h) (frameBorelFactor_mul G A g a k h)
  have hpower := section_character_power G A (frameBorelFactor G A g a k h) n
  exact hrule.trans (congrArg (fun t : Γ(Spec (.of A), ⊤) =>
    characterFrameEvaluation G (G.positiveRootCharacter ^ n)
      ((algSpec (.of K)).obj (.op A)) (k.left ≫ flagQuotient G)
      (a ≫ flagChartMap G g) (canonical_quotient G A g a k h) ≫
        Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (Spec (.of A)).ringCatSheaf) t)
    hpower)

end SchubertGeometry.CharacterLine
