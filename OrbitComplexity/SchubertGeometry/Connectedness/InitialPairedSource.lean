import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.PairedSmoothModels
import OrbitComplexity.SchubertGeometry.BSDH.RichardsonMap
import OrbitComplexity.SchubertGeometry.Cells.Proper
import OrbitComplexity.FrobeniusSplitting.Normality.FiniteArithmeticSchemes

/-! # An arithmetic source from the two reduced words

Properness of the paired endpoint supplies a finite affine cover of its
source. The smooth source model is chosen from this cover, with no initial
arithmetic model as input. Its coefficient ring and source are Noetherian.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting

namespace SchubertGeometry

universe u

private theorem proper_source {B : Scheme.{u}} {C D : Over B} (e : C ⟶ D)
    [IsProper e.left] [IsProper D.hom] : IsProper C.hom := by
  have h : IsProper (e.left ≫ D.hom) := inferInstance
  exact e.w ▸ h

private theorem absolute_affine_diagonal {K : Type u} [CommRing K]
    (X : Over (Spec (.of K))) [IsSeparated X.hom] :
    IsAffineHom (pullback.diagonal (terminal.from X.left)) := by
  let : IsSeparated (terminal.from X.left) := by
    rw [← terminal.comp_from X.hom]
    infer_instance
  infer_instance

private theorem model_finiteness {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) (C : Over (Spec (.of S)))
    [CompactSpace C.left] [LocallyOfFinitePresentation C.hom] :
    AlgebraicGeometry.IsNoetherian C.left ∧ QuasiSeparatedSpace C.left := by
  let : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
  obtain ⟨hn, _hqc, _hqs⟩ := finiteType_int_scheme_properties C.hom
  let : AlgebraicGeometry.IsNoetherian C.left := hn
  exact ⟨hn, inferInstance⟩

/-- Two reduced words construct a compact smooth arithmetic paired source,
with a Cartesian comparison to the paired source. -/
theorem exists_initial_paired_source
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced b) :
    ∃ (S : Subalgebra ℤ K) (C : Over (Spec (.of S)))
      (q : (pairedBSDHSource G a b).left ⟶ C.left),
      S.FG ∧ CompactSpace C.left ∧ QuasiSeparatedSpace C.left ∧
      Smooth C.hom ∧ LocallyOfFinitePresentation C.hom ∧
      IsPullback q (pairedBSDHSource G a b).hom C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) := by
  let X := pairedBSDHSource G a b
  let D := (richardsonVariety G
    (G.longestElement * ReductiveGroups.simpleWeylWord G.rootBase b)
    (ReductiveGroups.simpleWeylWord G.rootBase a)).toOver
  let e : X ⟶ D := pairedRichardsonMap G a b ha hb
  let : IsProper e.left := pairedRichardsonMap_isProper G a b ha hb
  let : IsProper D.hom := richardsonVariety_isProper G _ _
  let : IsProper X.hom := proper_source e
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsAffineHom (pullback.diagonal (terminal.from X.left)) :=
    absolute_affine_diagonal X
  let : LocallyOfFinitePresentation X.hom := inferInstance
  obtain ⟨I, finiteI, U, hU, hcover⟩ := exists_finite_affine_opens X.left
  let : Finite I := finiteI
  obtain ⟨S, C, q, hS, hcompact, hsmooth, hfp, hq⟩ :=
    exists_paired_smooth_model G a b U hU hcover
  let : CompactSpace C.left := hcompact
  let : LocallyOfFinitePresentation C.hom := hfp
  have hfinite := model_finiteness S hS C
  exact ⟨S, C, q, hS, hcompact, hfinite.2, hsmooth, hfp, hq⟩

end SchubertGeometry
