import OrbitComplexity.FrobeniusSplitting.Normality.PositiveSchemeFibres
import OrbitComplexity.SchubertGeometry.Normality.ScalarFibreNormality
import OrbitComplexity.SchubertGeometry.Normality.Coordinates.InitialNormalityModels
import OrbitComplexity.SchubertGeometry.Cells.RichardsonIntegral
import OrbitComplexity.SchubertGeometry.Cells.RichardsonSchubert
import OrbitComplexity.FrobeniusSplitting.Normality.FlatDescent
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Normality from split resolution fibres

A proper geometrically connected morphism with integral normal source fibres
gives normality on split positive-characteristic target fibres. Arithmetic
descent then gives normality on the integral generic target.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting ReductiveGroups

namespace SchubertGeometry

universe u

open private scalar_property
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected

/-- A proper geometrically connected resolution with integral normal field
fibres and split positive-characteristic target fibres proves normality of
the integral generic target on the prescribed Cartesian comparison. -/
theorem normal_stalks_of_split_resolutions {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG)
    (C D : Over (Spec (.of S))) [LocallyOfFinitePresentation D.hom]
    (e : C ⟶ D) [IsProper e.left] [GeometricallyConnected e.left]
    (X : Over (Spec (.of K))) [IsIntegral X.left]
    (q : X.left ⟶ D.left)
    (hq : IsPullback q X.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hsource : ∀ (L : Type u) [Field L] [Algebra S L],
      let β := Spec.map (CommRingCat.ofHom (algebraMap S L))
      IsIntegral (pullback β C.hom : Scheme.{u}) ∧
        ∀ x : (pullback β C.hom : Scheme.{u}),
          IsIntegrallyClosed ((pullback β C.hom : Scheme.{u}).presheaf.stalk x))
    (hsplit : ∀ (L : Type u) [Field L] [Algebra S L],
      ∀ (p : ℕ) [Fact p.Prime] [CharP L p],
        Nonempty (SchemeSplitting
          (pullback (Spec.map (CommRingCat.ofHom (algebraMap S L))) D.hom) p)) :
    ∀ x : X.left, IsDomain (X.left.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.left.presheaf.stalk x) := by
  apply normal_stalks_of_positive_fibres S hS D X q hq
  intro L _ _ hprime
  let β := Spec.map (CommRingCat.ofHom (algebraMap S L))
  let : Fact (ringChar L).Prime := ⟨hprime⟩
  obtain ⟨hIntegral, hn⟩ := hsource L
  let : IsIntegral (pullback β C.hom : Scheme.{u}) := hIntegral
  let : GeometricallyConnected (chosenScalarArrow β e).left :=
    scalar_property (fun _ _ f => GeometricallyConnected f) β e inferInstance
  let : IrreducibleSpace (Over.mk (pullback.fst β C.hom)).left :=
    (inferInstance : IrreducibleSpace (pullback β C.hom : Scheme.{u}))
  let g := (chosenScalarArrow β e).left
  let : IrreducibleSpace (pullback β D.hom : Scheme.{u}) :=
    g.surjective.irreducibleSpace g.continuous
  obtain ⟨σ⟩ := hsplit L (ringChar L)
  exact ⟨inferInstance, scalar_fibre_stalks C D e β hn σ⟩

/-- A Richardson variety indexed by two reduced words has integrally closed
local domains whenever its lower endpoint is below its upper endpoint. -/
theorem richardson_stalks_of_words {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)
    (hle : WeylBruhatLE G.rootBase
      (G.longestElement * simpleWeylWord G.rootBase b) (simpleWeylWord G.rootBase a)) :
    ∀ x : (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
        (simpleWeylWord G.rootBase a)).scheme,
      IsDomain ((richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
          (simpleWeylWord G.rootBase a)).scheme.presheaf.stalk x) ∧
        IsIntegrallyClosed
          ((richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
            (simpleWeylWord G.rootBase a)).scheme.presheaf.stalk x) := by
  have models := @exists_richardson_split_models.{u} K kField kClosed kZero G a b ha hb hle
  obtain ⟨S, C, D, F, e, j, qC, qD, qF, hS, _hCNoeth, _hDNoeth, _hFNoeth,
    _hCSmooth, _hCFP, hDFP, _hFFP, _hFSeparated, _hjClosed,
    _hC, _hD, _hF, _he, _hj, hStages, hSplits⟩ := models
  let start : CoefficientStage S := ⟨S, hS, le_rfl⟩
  have splittingBound := @hSplits start
  obtain ⟨bound, _hbound, hSplit⟩ := splittingBound
  have geometry := @hStages bound
  obtain ⟨t, hbt, hConnected, hProper, _hTargetConnected, hSource,
    _mC, mD, _mF, _hCt, hDt, _hFt, _hpC, _hpD, _hpF, _het, _hjt, _hjClosedt⟩ :=
    geometry
  let κ := Spec.map
    (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
  let Ct := @stageScalarModel.{u} K kField.toCommRing S C.left C.hom t
  let Dt := @stageScalarModel.{u} K kField.toCommRing S D.left D.hom t
  let et : Ct ⟶ Dt := chosenScalarArrow κ e
  let : LocallyOfFinitePresentation D.hom := hDFP
  let : LocallyOfFinitePresentation Dt.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst κ D.hom))
  let : IsProper et.left := hProper
  let : GeometricallyConnected et.left := hConnected
  have hIntegral : IsIntegral (richardsonVariety G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).scheme :=
    @richardsonVariety_integral.{u} K kField kClosed kZero G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a) hle
  refine @normal_stalks_of_split_resolutions.{u} K kField t.val t.property.1 Ct Dt
    (inferInstanceAs (LocallyOfFinitePresentation Dt.hom)) et
    (inferInstanceAs (IsProper et.left)) (inferInstanceAs (GeometricallyConnected et.left))
    (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).toOver hIntegral mD hDt ?_ ?_
  · intro L lField lAlgebra
    have fields := @hSource L lField
      (Spec.map (CommRingCat.ofHom (@algebraMap t.val L _ _ lAlgebra)))
    exact ⟨fields.1, fun x => (fields.2 x).2⟩
  · intro L lField lAlgebra p hpPrime lChar
    exact @hSplit t hbt L lField
      (Spec.map (CommRingCat.ofHom (@algebraMap t.val L _ _ lAlgebra))) p hpPrime lChar

/-- A nonempty Richardson variety has integrally closed local domains. -/
theorem richardson_normal_stalks {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (lower upper : G.weylGroup)
    (hle : WeylBruhatLE G.rootBase lower upper) :
    ∀ x : (richardsonVariety G lower upper).scheme,
      IsDomain ((richardsonVariety G lower upper).scheme.presheaf.stalk x) ∧
        IsIntegrallyClosed ((richardsonVariety G lower upper).scheme.presheaf.stalk x) := by
  obtain ⟨a, ha, hupper⟩ := (weylCoxeterSystem G.rootBase).exists_isReduced upper
  rw [weylCoxeterSystem_wordProd] at hupper
  obtain ⟨b, hb, hlower⟩ :=
    (weylCoxeterSystem G.rootBase).exists_isReduced (G.longestElement⁻¹ * lower)
  rw [weylCoxeterSystem_wordProd] at hlower
  have he : lower = G.longestElement * simpleWeylWord G.rootBase b := by
    rw [← hlower]
    group
  subst upper
  subst lower
  exact @richardson_stalks_of_words.{u} K kField kClosed kZero G a b ha hb hle

/-- A Schubert variety has integrally closed local domains. -/
theorem schubert_normal_stalks {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (w : G.weylGroup) :
    ∀ x : (schubertVariety G w).scheme,
      IsDomain ((schubertVariety G w).scheme.presheaf.stalk x) ∧
        IsIntegrallyClosed ((schubertVariety G w).scheme.presheaf.stalk x) := by
  let f : (richardsonVariety G 1 w).scheme ⟶ (schubertVariety G w).scheme :=
    (richardsonSchubertIso G w).hom.left
  let : IsIso f := inferInstanceAs (IsIso (richardsonSchubertIso G w).hom.left)
  exact @FrobeniusSplitting.stalks_of_flat_surjective.{u} _ _ f inferInstance inferInstance
    (@richardson_normal_stalks.{u} K kField kClosed kZero G 1 w
      ((weyl_bruhat_iff G.rootBase 1 w).mpr
        ((weylCoxeterSystem G.rootBase).one_bruhatLE w)))

end SchubertGeometry
