import OrbitComplexity.SchubertGeometry.Connectedness.ChosenIntegralModels
import OrbitComplexity.SchubertGeometry.Connectedness.ScalarModelComparisons
import OrbitComplexity.SchubertGeometry.Connectedness.SmoothFieldFibres
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.IntegralFamily
import Batteries.Tactic.Lint

/-! # Integral source fibres at one coefficient stage

Successive extensions of the prescribed paired model are identified with
one scalar extension, preserving the endpoint. Integral field fibres give
geometric connectedness, and smoothness supplies normal domain stalks.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u

namespace SchubertGeometry

/-- One coefficient stage of the prescribed paired model has a proper
geometrically connected endpoint, a geometrically connected Richardson
target, and integral normal-domain source fibres over every field. -/
theorem exists_chosen_integral_stage
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)
    (hab : WeylBruhatLE G.rootBase
      (G.longestElement * simpleWeylWord G.rootBase b) (simpleWeylWord G.rootBase a))
    (S : Subalgebra ℤ K) (hS : S.FG)
    (C D F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left] [Smooth C.hom]
    [CompactSpace D.left] [QuasiSeparatedSpace D.left]
    [LocallyOfFinitePresentation D.hom]
    [LocallyOfFinitePresentation F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
    (e : C ⟶ D) (r : D ⟶ F) [IsClosedImmersion r.left]
    (qC : (pairedBSDHSource G a b).left ⟶ C.left)
    (qD : (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).scheme ⟶ D.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hC : IsPullback qC (pairedBSDHSource G a b).hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD (richardsonVariety G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (he : qC ≫ e.left = (pairedRichardsonMap G a b ha hb).left ≫ qD)
    (hr : qD ≫ r.left = (richardsonInclusion G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).left ≫ qF)
    (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t),
      let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
      GeometricallyConnected (chosenScalarArrow κ e).left ∧
      IsProper (chosenScalarArrow κ e).left ∧
      GeometricallyConnected (stageScalarModel S D.hom t).hom ∧
      ∀ (L : Type u) [Field L] (s : Spec (.of L) ⟶ Spec (.of t.val)),
        IsIntegral (pullback s (stageScalarModel S C.hom t).hom : Scheme.{u}) ∧
        ∀ x : (pullback s (stageScalarModel S C.hom t).hom : Scheme.{u}),
          IsDomain ((pullback s (stageScalarModel S C.hom t).hom :
            Scheme.{u}).presheaf.stalk x) ∧
          IsIntegrallyClosed ((pullback s (stageScalarModel S C.hom t).hom :
            Scheme.{u}).presheaf.stalk x) := by
  obtain ⟨k, hk, l, hgc, hp, hDgc, hfields⟩ :=
    exists_chosen_integral_models G a b ha hb hab S hS C D F e r qC qD qF
      hC hD hF he hr start
  let t := singleScalarStage S k l
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
  let C₂ := stageScalarModel k.val (stageScalarModel S C.hom k).hom l
  let CT := stageScalarModel S C.hom t
  have hproperties := scalarModelIso_properties S k l e hp hgc hDgc
  have hC₂ : GeometricallyConnected C₂.hom :=
    geomConnected_of_integral_fibres C₂.hom (fun L _ s => (hfields L s).1)
  let : GeometricallyConnected CT.hom :=
    geomConnected_over_iso (scalarModelIso S k l C) hC₂
  let : Smooth CT.hom := by
    change Smooth (pullback.fst κ C.hom)
    infer_instance
  have hstart : start ≤ t := by
    change start.val ≤ l.val
    exact (show start.val ≤ k.val from hk).trans l.property.2
  exact ⟨t, hstart, hproperties.2.1, hproperties.1, hproperties.2.2,
    fun L _ s => integral_smooth_field_fibres CT L s⟩

end SchubertGeometry
