import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.ElementaryCurves
import OrbitComplexity.FrobeniusSplitting.Normality.IntegralSource
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Append and paired endpoint induction over arbitrary coefficient schemes

The append step takes specified correspondence squares and one of the two elementary
curve descriptions. Its sole preceding connectedness input is the earlier endpoint,
which is the induction hypothesis. The paired consumer takes specified endpoint product
and Cartesian comparison maps, including the chosen source isomorphism.
-/

open FrobeniusSplitting

noncomputable section

namespace SchubertGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped Polynomial

universe u v w

attribute [local instance] Over.cartesianMonoidalCategory

section Category

variable {C : Type v} [Category.{w} C] [HasPullbacks C]

/-- The fibre of a correspondence endpoint is the inverse image of its elementary curve. -/
def endpointRelativeFibreIso {N A X Y S F : C}
    (d : N ⟶ A) (n : N ⟶ X) (a : A ⟶ X) (π : X ⟶ Y)
    (y : S ⟶ X) (c : F ⟶ X) (t : F ⟶ S)
    (hg : IsPullback d n (a ≫ π) π) (hc : IsPullback c t π (y ≫ π)) :
    pullback n y ≅ pullback a c :=
  ((IsPullback.of_hasPullback n y).paste_horiz hg).isoPullback ≪≫
    ((IsPullback.of_hasPullback a c).paste_vert hc).isoPullback.symm


private def endpoint_mono_fibre_iso {N T X S : C} (m : N ⟶ T) (j : T ⟶ X)
    [Mono j] (y : S ⟶ T) : pullback m y ≅ pullback (m ≫ j) (y ≫ j) :=
  (limit.isoLimitCone ⟨_, pullbackIsPullbackOfCompMono m y j⟩).symm

end Category

/-- a specified product trivialization transports geometric connectedness of its constant fibre. -/
theorem endpoint_cell_product_gc {P C F S : Scheme.{u}}
    (bF : F ⟶ S) (bC : C ⟶ S) (m : P ⟶ C) [GeometricallyConnected bF]
    (e : P ≅ pullback bF bC) (he : e.hom ≫ pullback.snd bF bC = m) :
    GeometricallyConnected m := by
  rw [← he]
  exact geomConnected_comp_iso e (pullback.snd bF bC)

/-- Proper morphisms with connected geometric fibres compose without requiring openness. -/
theorem endpoint_proper_gc_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f] [GeometricallyConnected f] [GeometricallyConnected g] :
    GeometricallyConnected (f ≫ g) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro L _ z
  have : ConnectedSpace (pullback g z : Scheme.{u}) :=
    pullback_of_geometrically
      (inferInstance : GeometricallyConnected g).geometrically_connectedSpace L z
  rw [← (pullbackRightPullbackFstIso g z f).hom.homeomorph.connectedSpace_iff]
  exact connectedSpace_of_proper (pullback.snd f (pullback.fst g z))

private abbrev endpointProperGC : MorphismProperty Scheme.{u} :=
  @IsProper ⊓ @GeometricallyConnected

private theorem endpointProperGC_baseChange :
    MorphismProperty.IsStableUnderBaseChange (endpointProperGC.{u}) where
  of_isPullback h hh :=
    ⟨MorphismProperty.of_isPullback (P := @IsProper) h hh.1,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h hh.2⟩

private theorem endpointProperGC_compStable :
    MorphismProperty.IsStableUnderComposition (endpointProperGC.{u}) where
  comp_mem f g hf hg := by
    have : IsProper f := hf.1
    have : IsProper g := hg.1
    have : GeometricallyConnected f := hf.2
    have : GeometricallyConnected g := hg.2
    exact ⟨inferInstance, endpoint_proper_gc_comp f g⟩

end SchubertGeometry
