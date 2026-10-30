import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorOperator
import OrbitComplexity.FrobeniusSplitting.Splittings.Perfect
import OrbitComplexity.FrobeniusSplitting.Splittings.Spec
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorNormalization

/-! # The constructed empty-word twisted prior map

The initial character line is the unit line. The map is constructed from the
perfect ground field's splitting, without a prior operator.
-/

open AlgebraicGeometry CategoryTheory Opposite
open FrobeniusSplitting
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

variable (K : Type u) [Field K] (p : ℕ) [ExpChar K p] [PerfectRing K p]

private abbrev baseScheme := Spec (.of K)
private abbrev baseLine := SheafOfModules.unit (baseScheme K).ringCatSheaf
private abbrev baseSplitting :=
  (RingSplitting.ofPerfectRing K p).toSpec (expChar_pos K p)

private def baseUnit : (baseLine K).val.obj (op ⊤) := (1 : Γ(baseScheme K, ⊤))

/-- The empty-word map on the unit character line is the ground-field
splitting, regarded as a map from the Frobenius-restricted module. -/
def emptyTwistedPriorMap :
    frobeniusRestriction K p (𝟙 (baseScheme K)) (baseLine K) ⟶ baseLine K where
  val :=
    { app := fun U =>
        { hom' :=
          { toFun := fun a => (baseSplitting K p).onOpen U.unop a
            map_add' := fun a b => ((baseSplitting K p).onOpen U.unop).map_add a b
            map_smul' := fun a b => by
              let r : Γ(baseScheme K, U.unop) := a
              let s : Γ(baseScheme K, U.unop) := b
              change (baseSplitting K p).onOpen U.unop (r ^ p * s) =
                r * (baseSplitting K p).onOpen U.unop s
              exact ((baseSplitting K p).onOpen U.unop).map_pow_mul r s } }
      naturality := fun {U V} f => by
        ext a
        change (baseSplitting K p).onOpen V.unop
            ((baseScheme K).presheaf.map f a) =
          (baseScheme K).presheaf.map f ((baseSplitting K p).onOpen U.unop a)
        exact (baseSplitting K p).restrict_comm f.unop.le a }

/-- The initial section is the same unit section and has normalization one. -/
theorem emptyTwistedPriorMap_one :
    (emptyTwistedPriorMap K p).app ⊤ (baseUnit K) = baseUnit K := by
  change (baseSplitting K p).onOpen ⊤ 1 = 1
  exact ((baseSplitting K p).onOpen ⊤).map_one

/-- Inserting the empty-word unit section gives the already constructed
ground-field operator, with no second weight. -/
theorem emptyTwistedPriorMap_operator :
    twistedSectionOperator (𝟙 (baseScheme K)) (baseLine K) (emptyTwistedPriorMap K p)
      (baseUnit K) = (baseSplitting K p).toOperator := by
  apply SchemeFrobeniusMap.ext
  intro U a
  change (baseSplitting K p).onOpen U
      (a * (baseScheme K).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op 1) =
    (baseSplitting K p).onOpen U a
  rw [map_one, mul_one]

end SchubertGeometry.ProjectiveCartier
