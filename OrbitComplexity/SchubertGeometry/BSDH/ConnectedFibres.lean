import OrbitComplexity.SchubertGeometry.Parabolics.SimpleCurve
import OrbitComplexity.SchubertGeometry.Parabolics.CurveFibre
import OrbitComplexity.SchubertGeometry.BSDH.CellFibres
import OrbitComplexity.SchubertGeometry.BSDH.Surjectivity
import OrbitComplexity.SchubertGeometry.Cells.OrbitDecomposition
import OrbitComplexity.SchubertGeometry.Parabolics.Order
import OrbitComplexity.GroupActions.Varieties.GeometricCover
import OrbitComplexity.FrobeniusSplitting.Normality.IntegralSource

/-! # Connected geometric fibres of Schubert resolutions

The last simple correspondence reduces Weyl fibres to connected curve intersections.
Borel cell trivializations extend the induction to every geometric fibre.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open BruhatIntervals
universe u v

private def relativeFibreIso {C : Type u} [Category.{v} C] [HasPullbacks C]
    {N A X Y S F : C} (d : N ⟶ A) (n : N ⟶ X) (a : A ⟶ X) (π : X ⟶ Y)
    (y : S ⟶ X) (c : F ⟶ X) (t : F ⟶ S)
    (hg : IsPullback d n (a ≫ π) π) (hc : IsPullback c t π (y ≫ π)) :
    pullback n y ≅ pullback a c :=
  ((IsPullback.of_hasPullback n y).paste_horiz hg).isoPullback ≪≫
    ((IsPullback.of_hasPullback a c).paste_vert hc).isoPullback.symm

private def factorFibreIso {C : Type u} [Category.{v} C] [HasPullbacks C]
    {A Z X F : C} (f : A ⟶ Z) (j : Z ⟶ X) (c : F ⟶ X) :
    pullback (f ≫ j) c ≅ pullback f (pullback.snd c j) :=
  (((IsPullback.of_hasPullback f (pullback.snd c j)).flip.paste_horiz
    (IsPullback.of_hasPullback c j)).flip.isoPullback).symm

private theorem connected_fibre_factor {A Z X F : Scheme.{u}}
    (f : A ⟶ Z) (j : Z ⟶ X) (c : F ⟶ X)
    [IsProper f] [GeometricallyConnected f]
    [ConnectedSpace (pullback c j : Scheme.{u})] :
    ConnectedSpace (pullback (f ≫ j) c : Scheme.{u}) := by
  have : ConnectedSpace (pullback f (pullback.snd c j) : Scheme.{u}) :=
    FrobeniusSplitting.connectedSpace_of_proper (pullback.snd f (pullback.snd c j))
  exact (factorFibreIso f j c).hom.homeomorph.connectedSpace_iff.mpr inferInstance

private theorem shorter_last_step {S W : Type*} [Group W] {M : CoxeterMatrix S}
    (cs : CoxeterSystem M W) (v x : W) (i : S)
    (hv : ¬ cs.IsRightDescent v i) (hx : cs.BruhatLE x (v * cs.simple i)) :
    ∃ r : W, ¬ cs.IsRightDescent r i ∧ cs.BruhatLE r v ∧
      (x = r ∨ x = r * cs.simple i) := by
  have hvs : cs.IsRightDescent (v * cs.simple i) i :=
    cs.isRightDescent_iff_not_isRightDescent_mul.mpr (by
      simpa only [cs.simple_mul_simple_cancel_right] using hv)
  by_cases hxi : cs.IsRightDescent x i
  · refine ⟨x * cs.simple i, cs.isRightDescent_iff_not_isRightDescent_mul.mp hxi,
      ?_, Or.inr ?_⟩
    · simpa only [cs.simple_mul_simple_cancel_right] using
        (bruhatLE_descent_iff cs i hxi hvs).mp hx
    · simp only [cs.simple_mul_simple_cancel_right]
  · refine ⟨x, hxi, ?_, Or.inl rfl⟩
    simpa only [cs.simple_mul_simple_cancel_right] using
      bruhatLE_mul_of_ascent cs hx i hxi

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem positive_of_ascent (w : G.weylGroup) (i : G.rootBase.support)
    (h : ¬ (weylCoxeterSystem G.rootBase).IsRightDescent w i) :
    G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val) := by
  by_contra hp
  apply h
  change (weylCoxeterSystem G.rootBase).length
    (w * (weylCoxeterSystem G.rootBase).simple i) <
      (weylCoxeterSystem G.rootBase).length w
  rw [weylCoxeterSystem_simple, weylCoxeterSystem_length, weylCoxeterSystem_length]
  have hn := rootInversionCount_mul_simple_of_neg G.rootBase w i
    ((root_height_neg_iff_not_isPos G.rootBase _).mpr hp)
  omega

private theorem shorter_weyl_step (v x : G.weylGroup) (i : G.rootBase.support)
    (hv : ¬ (weylCoxeterSystem G.rootBase).IsRightDescent v i)
    (hx : WeylBruhatLE G.rootBase x
      (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) :
    ∃ r : G.weylGroup, G.rootBase.IsPos (G.rootSystem.weylGroupToPerm r i.val) ∧
      WeylBruhatLE G.rootBase r v ∧
        (x = r ∨ x = r * RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  have hx' := (weyl_bruhat_iff G.rootBase _ _).mp hx
  rw [← weylCoxeterSystem_simple] at hx'
  obtain ⟨r, hr, hrv, hxr⟩ := shorter_last_step (weylCoxeterSystem G.rootBase) v x i hv hx'
  refine ⟨r, positive_of_ascent G r i hr, (weyl_bruhat_iff G.rootBase _ _).mpr hrv, ?_⟩
  simpa only [weylCoxeterSystem_simple] using hxr

private theorem partial_weyl_step (r x : G.weylGroup) (i : G.rootBase.support)
    (hx : x = r ∨ x = r * RootPairing.weylGroup.ofIdx G.rootSystem i.val) :
    (weylFlagPoint G r).val ≫ (partialFlagMorphism G {i}).left =
      (weylFlagPoint G x).val ≫ (partialFlagMorphism G {i}).left := by
  have hp : Variety.mapPoints (partialFlagMorphism G {i}) (weylFlagPoint G r) =
      Variety.mapPoints (partialFlagMorphism G {i}) (weylFlagPoint G x) := by
    change Variety.mapPoints (partialFlagMorphism G {i})
        (flagVarietyPointsEquiv G (flagProjection G (G.weylPoint r))) =
      Variety.mapPoints (partialFlagMorphism G {i})
        (flagVarietyPointsEquiv G (flagProjection G (G.weylPoint x)))
    rw [partialFlagMorphism_points, partialFlagMorphism_points]
    apply congrArg (partialFlagPointsEquiv G {i})
    apply (partialWeylFlag_eq_iff G {i} r x).mpr
    rcases hx with rfl | rfl
    · simp only [inv_mul_cancel]
      exact (standardParabolicSubgroup G.rootBase {i}).one_mem
    · simpa only [inv_mul_cancel_left] using
        simple_mem_standardParabolicSubgroup G.rootBase {i} i (Set.mem_singleton i)
  exact congrArg Subtype.val hp

section AppendSquare
variable (word : List G.rootBase.support) (i : G.rootBase.support)

private abbrev simpleFibre : Variety K :=
  schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)

private abbrev simpleProjection : flagBundleScheme G (simpleFibre G i) ⟶
    (flagVariety G).scheme := flagBundleProjection G (simpleFibre G i)

private abbrev simpleEndpoint : flagBundleScheme G (simpleFibre G i) ⟶
    (flagVariety G).scheme := flagBundleMap G (simpleFibre G i)
      (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))

private theorem append_square :
    IsPullback (bsdhAppendFst G word i) (bsdhMap G (word ++ [i]))
      (bsdhMap G word ≫ (partialFlagMorphism G {i}).left)
      (partialFlagMorphism G {i}).left := by
  let π := (partialFlagMorphism G {i}).left
  obtain ⟨e, he₁, he₂⟩ := simpleSchubert_incidence G i
  have hinc : IsPullback (simpleProjection G i) (simpleEndpoint G i) π π :=
    (IsPullback.of_hasPullback π π).of_iso' e (.refl _) (.refl _) (.refl _)
      (by simpa only [Iso.refl_hom, Category.comp_id] using he₁)
      (by simpa only [Iso.refl_hom, Category.comp_id] using he₂) (by simp) (by simp)
  have hp : IsPullback (pullback.fst (bsdhMap G word) (simpleProjection G i))
      (pullback.snd (bsdhMap G word) (simpleProjection G i) ≫ simpleEndpoint G i)
      (bsdhMap G word ≫ π) π :=
    ((IsPullback.of_hasPullback (bsdhMap G word) (simpleProjection G i)).flip.paste_horiz
      hinc.flip).flip
  let a : bsdhScheme G (word ++ [i]) ≅
      pullback (bsdhMap G word) (simpleProjection G i) :=
    (Over.forget (flagVariety G).scheme).mapIso (bsdhAppendIso G word i)
  have ha : a.hom ≫ pullback.snd (bsdhMap G word) (simpleProjection G i) ≫
      simpleEndpoint G i = bsdhMap G (word ++ [i]) :=
    bsdhAppendIso_endpoint G word i
  exact hp.of_iso' a (.refl _) (.refl _) (.refl _)
    (by rfl) (by simpa only [Iso.refl_hom, Category.comp_id] using ha) (by rfl) (by rfl)

end AppendSquare

private theorem append_weyl_connected (word : List G.rootBase.support)
    (i : G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced (word ++ [i]))
    (hprefix : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hprev : GeometricallyConnected (bsdhSchubertMap G word hprefix).left)
    (x : G.weylGroup)
    (hx : WeylBruhatLE G.rootBase x (simpleWeylWord G.rootBase (word ++ [i]))) :
    ConnectedSpace
      (pullback (bsdhMap G (word ++ [i])) (weylFlagPoint G x).val : Scheme.{u}) := by
  let v := simpleWeylWord G.rootBase word
  have hpos := isPos_of_reduced_append G.rootBase word i
    ((weylCoxeterSystem_isReduced_iff G.rootBase (word ++ [i])).mp hred)
  have hv : ¬ (weylCoxeterSystem G.rootBase).IsRightDescent v i := by
    intro hdesc
    change (weylCoxeterSystem G.rootBase).length
      (v * (weylCoxeterSystem G.rootBase).simple i) <
        (weylCoxeterSystem G.rootBase).length v at hdesc
    rw [weylCoxeterSystem_simple, weylCoxeterSystem_length,
      weylCoxeterSystem_length] at hdesc
    have hcount := rootInversionCount_mul_simple_of_pos G.rootBase v i hpos
    omega
  rw [simpleWeylWord_append_singleton] at hx
  obtain ⟨r, hr, hrv, hxr⟩ := shorter_weyl_step G v x i hv hx
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let π := (partialFlagMorphism G {i}).left
  let c : Y.toOver ⟶ (flagVariety G).toOver := simpleSchubertCurve G r i
  have hc : IsPullback c.left Y.toSpec π ((weylFlagPoint G r).val ≫ π) :=
    simpleSchubertCurve_isPullback G r i
  have hproject : (weylFlagPoint G r).val ≫ π = (weylFlagPoint G x).val ≫ π :=
    partial_weyl_step G r x i hxr
  rw [hproject] at hc
  let f := (bsdhSchubertMap G word hprefix).left
  let j := (schubertInclusion G v).left
  let : GeometricallyConnected f := hprev
  have hconn : ConnectedSpace (pullback c.left j : Scheme.{u}) :=
    simpleCurve_intersection_connected G r i v hr hrv
  let := hconn
  have hfactor : ConnectedSpace (pullback (f ≫ j) c.left : Scheme.{u}) :=
    connected_fibre_factor f j c.left
  have hcomp : f ≫ j = bsdhMap G word := bsdhSchubertMap_comp G word hprefix
  rw [hcomp] at hfactor
  let eF := relativeFibreIso (bsdhAppendFst G word i)
    (bsdhMap G (word ++ [i])) (bsdhMap G word) π (weylFlagPoint G x).val
    c.left Y.toSpec (append_square G word i) hc
  exact eF.hom.homeomorph.connectedSpace_iff.mpr hfactor

private theorem nil_schubert_connected
    (hred : (weylCoxeterSystem G.rootBase).IsReduced []) :
    GeometricallyConnected (bsdhSchubertMap G [] hred).left := by
  let f : Spec (CommRingCat.of K) ⟶ (schubertVariety G 1).scheme :=
    (bsdhSchubertMap G [] hred).left
  have hf : f ≫ (schubertVariety G 1).toSpec = 𝟙 _ := by
    have hw : f ≫ (schubertVariety G 1).toSpec =
        (baseFlagPoint G).val ≫ (flagVariety G).toSpec :=
      (bsdhSchubertMap G [] hred).w
    exact hw.trans (baseFlagPoint G).property
  let : IsClosedImmersion f :=
    isClosedImmersion_of_comp_eq_id (schubertVariety G 1).toSpec f hf
  let : Surjective f := bsdhSchubertMap_surjective G [] hred
  let : IsIso f := isIso_of_isClosedImmersion_of_surjective f
  change GeometricallyConnected f
  constructor
  intro L hL y Z a b h
  have : IsIso b := by
    rw [← h.isoPullback_hom_snd]
    infer_instance
  exact b.homeomorph.connectedSpace_iff.mpr inferInstance

/-- The reduced-word Schubert endpoint has connected geometric fibres. -/
theorem bsdhSchubert_geomConnected (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    GeometricallyConnected (bsdhSchubertMap G word hred).left := by
  induction word using List.reverseRecOn with
  | nil => exact nil_schubert_connected G hred
  | append_singleton word i ih =>
    have hprefix : (weylCoxeterSystem G.rootBase).IsReduced word := by
      simpa using hred.take word.length
    have hprev : GeometricallyConnected (bsdhSchubertMap G word hprefix).left := ih hprefix
    let v := simpleWeylWord G.rootBase (word ++ [i])
    let indices := {x : G.weylGroup // WeylBruhatLE G.rootBase x v}
    let Z : indices → Scheme.{u} := fun x => (schubertCell G x.val).scheme
    let c : ∀ x : indices, Z x ⟶ (schubertVariety G v).scheme := fun x =>
      (schubertCellOfLE G x.val v x.property).left
    apply geometricallyConnected_of_cover (bsdhSchubertMap G (word ++ [i]) hred).left Z c
    · intro q
      obtain ⟨x, hx, _⟩ := schubertLowerCells_partition G v q
      exact ⟨x, hx⟩
    · intro x
      have hconn : ConnectedSpace (pullback (bsdhMap G (word ++ [i]))
          (weylFlagPoint G x.val).val : Scheme.{u}) :=
        append_weyl_connected G word i hred hprefix hprev x.val x.property
      exact bsdhCell_geomConnected G (word ++ [i])
        hred x.val x.property hconn

end SchubertGeometry
