import OrbitComplexity.SchubertGeometry.Connectedness.PairedEndpointStage
import OrbitComplexity.SchubertGeometry.Connectedness.RichardsonModelConnected
import OrbitComplexity.SchubertGeometry.Connectedness.PairedIntegral
import OrbitComplexity.FrobeniusSplitting.Normality.Smooth
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Integral fibres of the prescribed paired source

The paired endpoint and its Richardson target become geometrically
connected on one coefficient stage. Smoothness supplies domain and normal
stalks, and connectedness then gives integral fibres of the same source.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u

namespace SchubertGeometry

open private extended_chosen
  from OrbitComplexity.SchubertGeometry.Connectedness.PairedEndpointStage
open private scalar_property scalar_fp
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected
open private RetainedComparisons retained_comparisons
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointConnected

private theorem cartesian_morphism {B B' : Scheme.{u}} (κ : B' ⟶ B)
    {X Y : Over B} {X' Y' : Over B'}
    (tX : X'.left ⟶ X.left) (tY : Y'.left ⟶ Y.left)
    (hX : IsPullback tX X'.hom X.hom κ)
    (hY : IsPullback tY Y'.hom Y.hom κ)
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : tX ≫ f.left = f'.left ≫ tY) :
    IsPullback tX f'.left f.left tY := by
  have houter : IsPullback tX (f'.left ≫ Y'.hom) (f.left ≫ Y.hom) κ := by
    simpa only [f'.w, f.w] using hX
  exact houter.of_bot h hY

private theorem stage_property_mono {K : Type u} [CommRing K]
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (S : Subalgebra ℤ K) {C D : Over (Spec (.of S))} (e : C ⟶ D)
    {i j : CoefficientStage S} (hij : i ≤ j)
    (h : P (chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) e).left) :
    P (chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) e).left := by
  let κi := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let κj := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hij).toRingHom)
  let f := chosenScalarArrow κi e
  let f' := extendModelMorphism S C.hom D.hom hij f
  have hcart := cartesian_morphism τ
    (stageScalarTransition S C.hom hij) (stageScalarTransition S D.hom hij)
    (stageScalarCartesian S C.hom hij) (stageScalarCartesian S D.hom hij)
    f f' (extendModelMorphism_transition S C.hom D.hom hij f).symm
  have hf' : P f'.left := MorphismProperty.of_isPullback (P := P) hcart h
  have heq : f' = chosenScalarArrow κj e := extended_chosen S e hij
  exact (congrArg Over.Hom.left heq) ▸ hf'

private theorem integral_field_fibres {B : Scheme.{u}} {C D : Over B}
    [Smooth C.hom] [LocallyOfFinitePresentation D.hom]
    (e : C ⟶ D) [IsProper e.left] [GeometricallyConnected e.left]
    [GeometricallyConnected D.hom]
    (L : Type u) [Field L] (s : Spec (.of L) ⟶ B) :
    IsIntegral (pullback s C.hom : Scheme.{u}) ∧
      ∀ x : (pullback s C.hom : Scheme.{u}),
        IsDomain ((pullback s C.hom : Scheme.{u}).presheaf.stalk x) ∧
        IsIntegrallyClosed ((pullback s C.hom : Scheme.{u}).presheaf.stalk x) := by
  let CL : Over (Spec (.of L)) := Over.mk (pullback.fst s C.hom)
  let DL : Over (Spec (.of L)) := Over.mk (pullback.fst s D.hom)
  let eL : CL ⟶ DL := chosenScalarArrow s e
  let : IsProper eL.left := scalar_property (@IsProper) s e inferInstance
  let : GeometricallyConnected eL.left :=
    scalar_property (@GeometricallyConnected) s e inferInstance
  let : Smooth CL.hom := by
    change Smooth (pullback.fst s C.hom)
    infer_instance
  let : LocallyOfFinitePresentation DL.hom := scalar_fp s D
  let : GeometricallyConnected DL.hom := by
    change GeometricallyConnected (pullback.fst s D.hom)
    infer_instance
  let : ConnectedSpace DL.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton DL.hom
  have hstalks := FrobeniusSplitting.stalks_of_smooth CL.hom
  exact ⟨isIntegral_of_connected_endpoint DL.hom eL.left (fun x => (hstalks x).1),
    hstalks⟩

/-- The prescribed smooth paired source has integral field fibres after a
coefficient enlargement. Its scalar-extended endpoint is proper and
geometrically connected, its Richardson target has connected fibres, and
all three original comparison projections and endpoint triangles persist. -/
theorem exists_paired_integral_model {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)
    (hab : WeylBruhatLE G.rootBase
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a))
    (S : Subalgebra ℤ K) (hS : S.FG)
    (C D X Y U V F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [Smooth C.hom]
    [CompactSpace D.left] [QuasiSeparatedSpace D.left]
    [LocallyOfFinitePresentation D.hom]
    [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
    [IsProper Y.hom] [LocallyOfFinitePresentation Y.hom]
    [LocallyOfFinitePresentation U.hom] [LocallyOfFinitePresentation V.hom]
    [LocallyOfFinitePresentation F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
    (e : C ⟶ D) (r : D ⟶ F) [IsClosedImmersion r.left]
    (f : X ⟶ U) (g : Y ⟶ V) [IsProper f.left] [IsProper g.left]
    (i : U ⟶ F) (j : V ⟶ F) [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (qX : bsdhScheme G a ⟶ X.left) (qY : bsdhScheme G b ⟶ Y.left)
    (qU : (schubertVariety G (simpleWeylWord G.rootBase a)).scheme ⟶ U.left)
    (qV : (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase b)).scheme ⟶ V.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qC : (pairedBSDHSource G a b).left ⟶ C.left)
    (qD : (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).scheme ⟶ D.left)
    (hX : IsPullback qX (bsdhToSpec G a) X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY (bsdhToSpec G b) Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hU : IsPullback qU (schubertVariety G (simpleWeylWord G.rootBase a)).toSpec U.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hV : IsPullback qV (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase b)).toSpec V.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hC : IsPullback qC (pairedBSDHSource G a b).hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD (richardsonVariety G
      (G.longestElement * simpleWeylWord G.rootBase b) (simpleWeylWord G.rootBase a)).toSpec
      D.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hf : qX ≫ f.left = (bsdhSchubertMap G a ha).left ≫ qU)
    (hg : qY ≫ g.left = (bsdhOppositeSchubertMap G b hb).left ≫ qV)
    (hi : qU ≫ i.left = (schubertInclusion G (simpleWeylWord G.rootBase a)).left ≫ qF)
    (hj : qV ≫ j.left = (oppositeSchubertInclusion G
      (G.longestElement * simpleWeylWord G.rootBase b)).left ≫ qF)
    (he : qC ≫ e.left = (pairedRichardsonMap G a b ha hb).left ≫ qD)
    (hr : qD ≫ r.left = (richardsonInclusion G
      (G.longestElement * simpleWeylWord G.rootBase b) (simpleWeylWord G.rootBase a)).left ≫ qF)
    (start : CoefficientStage S) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k),
      let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
      GeometricallyConnected (chosenScalarArrow κ e).left ∧
      IsProper (chosenScalarArrow κ e).left ∧
      GeometricallyConnected (stageScalarModel S D.hom k).hom ∧
      (∀ (L : Type u) [Field L] (s : Spec (.of L) ⟶ Spec (.of k.val)),
        IsIntegral (pullback s (stageScalarModel S C.hom k).hom : Scheme.{u}) ∧
        ∀ x : (pullback s (stageScalarModel S C.hom k).hom : Scheme.{u}),
          IsDomain ((pullback s (stageScalarModel S C.hom k).hom :
            Scheme.{u}).presheaf.stalk x) ∧
          IsIntegrallyClosed ((pullback s (stageScalarModel S C.hom k).hom :
            Scheme.{u}).presheaf.stalk x)) ∧
      RetainedComparisons S C D F e r (pairedBSDHSource G a b)
        (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
          (simpleWeylWord G.rootBase a)).toOver (flagVariety G).toOver
        (pairedRichardsonMap G a b ha hb)
        (richardsonInclusion G (G.longestElement * simpleWeylWord G.rootBase b)
          (simpleWeylWord G.rootBase a)) qC qD qF k := by
  obtain ⟨_qP, _hP, _hProjX, _hProjY, k, hk, _E, _hEhom, _hEinv,
    _A, _hAEnd, _hAProjX, _hAProjY, hgc, hp, _hbase, _hold, _hfields, _hretained⟩ :=
    exists_paired_endpoint_connected G a b ha hb S hS C D X Y U V F
      e r f g i j qX qY qU qV qF qC qD hX hY hU hV hF hC hD hf hg hi hj he hr start
  obtain ⟨t, hkt, hDgc, _qT, _hDT, _hOriginalT⟩ :=
    exists_richardson_model_connected G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a) hab S D qD hD k
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
  let CT := stageScalarModel S C.hom t
  let DT := stageScalarModel S D.hom t
  let et : CT ⟶ DT := chosenScalarArrow κ e
  have hgcT : GeometricallyConnected et.left :=
    stage_property_mono (@GeometricallyConnected) S e hkt hgc
  have hpT : IsProper et.left := stage_property_mono (@IsProper) S e hkt hp
  let : GeometricallyConnected et.left := hgcT
  let : IsProper et.left := hpT
  let : GeometricallyConnected DT.hom := hDgc
  let : LocallyOfFinitePresentation DT.hom := scalar_fp κ D
  let : Smooth CT.hom := by
    change Smooth (pullback.fst κ C.hom)
    infer_instance
  have hretained := retained_comparisons S C D F e r (pairedBSDHSource G a b)
    (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).toOver (flagVariety G).toOver
    (pairedRichardsonMap G a b ha hb)
    (richardsonInclusion G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)) qC qD qF hC hD hF he hr t
  exact ⟨t, hk.trans hkt, hgcT, hpT, hDgc,
    (fun L _ s => integral_field_fibres et L s), hretained⟩

end SchubertGeometry
