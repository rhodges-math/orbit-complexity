import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenFrameRestriction
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameNaturality
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Restriction of the adjusted matching frames

The generic open-triangle calculation identifies the incoming range section
with the inverse of the pulled-back coframe. The matching coframe's specified
refinement equation then identifies it with the selected frame on that node.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter
namespace SchubertGeometry.RetainedCharacter
universe u

open private originalLeg originalLegOpen
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitFrames
open private retainedChartRange
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts
open private range_triangle_le
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenFrameRestriction
open private rangeSection
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameSections
open private framePullbackIso
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameNaturality

variable {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)

private theorem retainedRange_le {s t : {s : Finset J // s.Nonempty}} (f : s ⟶ t) :
    retainedChartRange N cN hcN t ≤ retainedChartRange N cN hcN s := by
  exact @range_triangle_le _ _ _ (nodeMap N cN f).left
    (originalLeg N cN s) (originalLeg N cN t) (nodeMap N cN f).w
    (hopen f) (originalLegOpen N cN hcN s) (originalLegOpen N cN hcN t)

variable
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))

/-- Restricting an adjusted matching frame gives the adjusted frame of the
same index with the specified transported unit on the refined node. -/
theorem retainedMatchingFrame_restrict {s t : {s : Finset J // s.Nonempty}}
    (f : s ⟶ t) (j : J) (hj : j ∈ s.val) (d : (N.obj s)ˣ) (e : (N.obj t)ˣ)
    (hd : Units.map (N.map f).hom.toMonoidHom d = e) :
    (matchingModule N cN delta n).presheaf.map (homOfLE (retainedRange_le N cN hcN f)).op
        (retainedMatchingFrameSection N cN hcN delta n hco hn s j hj d) =
      retainedMatchingFrameSection N cN hcN delta n hco hn t j ((leOfHom f) hj) e := by
  have hg := @ProjectiveCartier.openFrameSection_triangle _ _ _ (nodeMap N cN f).left
    (originalLeg N cN s) (originalLeg N cN t) (nodeMap N cN f).w
    (hopen f) (originalLegOpen N cN hcN s) (originalLegOpen N cN hcN t)
    (matchingModule N cN delta n) (adjustedMatchingFrame N cN hcN delta n hco hn s j hj d)
  have ht := adjustedMatchingFrame_range_refine N cN hcN delta n hco hn f j hj d e hd
  exact hg.symm.trans ht

end SchubertGeometry.RetainedCharacter
