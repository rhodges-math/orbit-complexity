import OrbitComplexity.SchubertGeometry.Normality.Coordinates.FibreKernelModels
import OrbitComplexity.SchubertGeometry.Connectedness.ChosenIntegralStage
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelStageMaps
import Batteries.Tactic.Lint

/-! # Integral source fibres and Cartesian Richardson models on later stages -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting ReductiveGroups
namespace SchubertGeometry
universe u


/-- Above every coefficient stage, a Richardson resolution has a proper
geometrically connected endpoint and integral normal source fibres. The scalar
extensions retain the Cartesian comparisons and both inclusion triangles. -/
def normalityStages {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)
    (S : Subalgebra ℤ K) (C D F : Over (Spec (.of S)))
    (e : C ⟶ D) (j : D ⟶ F)
    (qC : (pairedBSDHSource G a b).left ⟶ C.left)
    (qD : (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).scheme ⟶ D.left)
    (qF : (flagVariety G).scheme ⟶ F.left) : Prop :=
  ∀ start : CoefficientStage S,
    ∃ (t : CoefficientStage S) (_ : start ≤ t),
      let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
      let ρ := Spec.map (CommRingCat.ofHom (algebraMap t.val K))
      GeometricallyConnected (chosenScalarArrow κ e).left ∧
      IsProper (chosenScalarArrow κ e).left ∧
      GeometricallyConnected (stageScalarModel S D.hom t).hom ∧
      (∀ (L : Type u) [Field L] (s : Spec (.of L) ⟶ Spec (.of t.val)),
        IsIntegral (pullback s (stageScalarModel S C.hom t).hom : Scheme.{u}) ∧
        ∀ x : (pullback s (stageScalarModel S C.hom t).hom : Scheme.{u}),
          IsDomain ((pullback s (stageScalarModel S C.hom t).hom : Scheme.{u}).presheaf.stalk x) ∧
          IsIntegrallyClosed
            ((pullback s (stageScalarModel S C.hom t).hom : Scheme.{u}).presheaf.stalk x)) ∧
      ∃ (mC : (pairedBSDHSource G a b).left ⟶ (stageScalarModel S C.hom t).left)
        (mD : (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
          (simpleWeylWord G.rootBase a)).scheme ⟶ (stageScalarModel S D.hom t).left)
        (mF : (flagVariety G).scheme ⟶ (stageScalarModel S F.hom t).left),
        IsPullback mC (pairedBSDHSource G a b).hom (stageScalarModel S C.hom t).hom ρ ∧
        IsPullback mD (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
          (simpleWeylWord G.rootBase a)).toSpec (stageScalarModel S D.hom t).hom ρ ∧
        IsPullback mF (flagVariety G).toSpec (stageScalarModel S F.hom t).hom ρ ∧
        mC ≫ pullback.snd κ C.hom = qC ∧
        mD ≫ pullback.snd κ D.hom = qD ∧
        mF ≫ pullback.snd κ F.hom = qF ∧
        mC ≫ (chosenScalarArrow κ e).left = (pairedRichardsonMap G a b ha hb).left ≫ mD ∧
        mD ≫ (chosenScalarArrow κ j).left = (richardsonInclusion G
          (G.longestElement * simpleWeylWord G.rootBase b)
          (simpleWeylWord G.rootBase a)).left ≫ mF ∧
        IsClosedImmersion (chosenScalarArrow κ j).left

/-- The prescribed smooth paired source and closed Richardson target retain
their resolution geometry above every coefficient stage. -/
theorem exists_chosen_normality_models
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)
    (hab : WeylBruhatLE G.rootBase
      (G.longestElement * simpleWeylWord G.rootBase b) (simpleWeylWord G.rootBase a))
    (S : Subalgebra ℤ K) (hS : S.FG) (C D F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left] [Smooth C.hom]
    [CompactSpace D.left] [QuasiSeparatedSpace D.left]
    [LocallyOfFinitePresentation D.hom]
    [LocallyOfFinitePresentation F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
    (e : C ⟶ D) (j : D ⟶ F) [IsClosedImmersion j.left]
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
    (hj : qD ≫ j.left = (richardsonInclusion G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).left ≫ qF)
 :
    @normalityStages.{u} K (inferInstanceAs (Field K))
      (inferInstanceAs (IsAlgClosed K)) (inferInstanceAs (CharZero K))
      G a b ha hb S C D F e j qC qD qF := by
  intro start
  have hIntegral :=
    @exists_chosen_integral_stage.{u} K
      (inferInstanceAs (Field K)) (inferInstanceAs (IsAlgClosed K))
      (inferInstanceAs (CharZero K)) G a b ha hb hab S hS C D F
      (inferInstanceAs (CompactSpace C.left)) (inferInstanceAs (QuasiSeparatedSpace C.left))
      (inferInstanceAs (Smooth C.hom)) (inferInstanceAs (CompactSpace D.left))
      (inferInstanceAs (QuasiSeparatedSpace D.left))
      (inferInstanceAs (LocallyOfFinitePresentation D.hom))
      (inferInstanceAs (LocallyOfFinitePresentation F.hom))
      (inferInstanceAs (QuasiCompact F.hom)) (inferInstanceAs (IsSeparated F.hom))
      e j (inferInstanceAs (IsClosedImmersion j.left)) qC qD qF hC hD hF he hj start
  obtain ⟨t, ht, hgc, hp, hDgc, hsource⟩ := hIntegral
  let v := G.longestElement * simpleWeylWord G.rootBase b
  let w := simpleWeylWord G.rootBase a
  let eK := pairedRichardsonMap G a b ha hb
  let jK := richardsonInclusion G v w
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap t.val K))
  let σ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  have hρ : ρ ≫ κ = σ := by rw [← Spec.map_comp]; rfl
  have hEbase := map_to_variety_base (pairedBSDHSource G a b)
    (richardsonVariety G v w) eK
  have hJbase := varietyMap_base (richardsonVariety G v w) (flagVariety G) jK
  have hComparisons :=
    @diagram_stage_comparisons.{u} (Spec (.of S)) (Spec (.of t.val)) (Spec (.of K))
      (pairedBSDHSource G a b).left (richardsonVariety G v w).scheme
      (flagVariety G).scheme κ ρ σ hρ C D F
      (pairedBSDHSource G a b).hom (richardsonVariety G v w).toSpec (flagVariety G).toSpec
      eK.left jK.left hEbase hJbase e j qC qD qF hC hD hF he hj
  obtain ⟨mC, mD, mF, hCt, hDt, hFt, hpC, hpD, hpF, het, hjt⟩ := hComparisons
  have hclosed : IsClosedImmersion (chosenScalarArrow κ j).left :=
    MorphismProperty.of_isPullback (chosenScalarArrow_cartesian κ j).flip
      (inferInstance : IsClosedImmersion j.left)
  exact ⟨t, ht, hgc, hp, hDgc, hsource,
    mC, mD, mF, hCt, hDt, hFt, hpC, hpD, hpF, het, hjt, hclosed⟩

end SchubertGeometry
