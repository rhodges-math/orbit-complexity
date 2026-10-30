import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionMatchingFactors
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage
import Batteries.Tactic.Lint

/-! # Refinements of the opposition-chart preimage

The original word identification fixes the structure map of the opposition-chart
preimage. Scalar coordinate charts then retain that same structure map.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry.RetainedCharacter

open private SchubertGeometry.CharacterLine.U from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private SchubertGeometry.RetainedCharacter.preimageSnd
  SchubertGeometry.RetainedCharacter.preimageLift
  SchubertGeometry.RetainedCharacter.preimageLift_equation
  SchubertGeometry.RetainedCharacter.schemeSource from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage

private theorem schemeSource_base {k : Type u} [Field k] (V : Variety k)
    (W : Over (Spec (.of k))) (f : V.toOver ⟶ W) :
    SchubertGeometry.RetainedCharacter.schemeSource V f.left ≫ W.hom = V.toOver.hom :=
  f.w

private theorem chart_base {P U V W L B : Scheme.{u}}
    (a : P ⟶ U) (c : U ⟶ V) (t : P ⟶ W) (q : W ⟶ L) (g : L ⟶ V)
    (bU : U ⟶ B) (bV : V ⟶ B) (bL : L ⟶ B) (bW : W ⟶ B)
    (hc : c ≫ bV = bU) (hg : g ≫ bV = bL) (hq : q ≫ bL = bW)
    (h : a ≫ c = (t ≫ q) ≫ g) : a ≫ bU = t ≫ bW := by
  calc
    a ≫ bU = a ≫ (c ≫ bV) := congrArg (a ≫ ·) hc.symm
    _ = (a ≫ c) ≫ bV := (Category.assoc _ _ _).symm
    _ = ((t ≫ q) ≫ g) ≫ bV := congrArg (· ≫ bV) h
    _ = (t ≫ q) ≫ (g ≫ bV) := Category.assoc _ _ _
    _ = (t ≫ q) ≫ bL := congrArg ((t ≫ q) ≫ ·) hg
    _ = t ≫ (q ≫ bL) := Category.assoc _ _ _
    _ = t ≫ bW := congrArg (t ≫ ·) hq

/-- The structure map of the opposition-chart preimage agrees with the
structure map of the original word colimit under its fixed identification. -/
theorem wordChartPreimage_base {K : Type u}
    [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (C : Over (Spec (.of K))) (q : C.left ⟶ bsdhScheme G word)
    (hword : q ≫ bsdhToSpec G word = C.hom)
    (i : G.rootBase.support) :
    SchubertGeometry.RetainedCharacter.preimageLift G word q i ≫ (oppositeUnipotentVariety
      G).toOver.hom =
      SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫ C.hom := by
  have hchart := @schemeSource_base K hK (oppositeUnipotentVariety G)
    (flagVariety G).toOver
    (flagChartMorphism G (DeterminantSection.oppositionChartPoint G i))
  have hequation := @SchubertGeometry.RetainedCharacter.preimageLift_equation
    K hK hAlg hChar G C.left word q i
  exact @chart_base (wordChartPreimage G word q i)
    (SchubertGeometry.CharacterLine.U G) (flagVariety G).scheme C.left
    (bsdhScheme G word) (Spec (.of K))
    (SchubertGeometry.RetainedCharacter.preimageLift G word q i)
    (SchubertGeometry.RetainedCharacter.schemeSource (oppositeUnipotentVariety G)
      (flagChartMorphism G (DeterminantSection.oppositionChartPoint G i)).left)
    (SchubertGeometry.RetainedCharacter.preimageSnd G word q i) q (bsdhMap G word)
    (oppositeUnipotentVariety G).toOver.hom (flagVariety G).toSpec
    (bsdhToSpec G word) C.hom hchart rfl hword hequation

end SchubertGeometry.RetainedCharacter
