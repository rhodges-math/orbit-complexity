import OrbitComplexity.SchubertGeometry.BSDH.PointedCell
import OrbitComplexity.FrobeniusSplitting.Normality.Models.PointedOpenIso
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.BirationalSchemeStages
import Batteries.Tactic.Lint

/-! # Birational field fibres of longest-word endpoints

The longest Schubert cell supplies the affine common chart and its rational
point. Its comparison with prescribed arithmetic word and flag models retains
birationality at one coefficient stage, with the original projections.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReductiveGroups GroupActions FrobeniusSplitting

namespace SchubertGeometry

universe u

private theorem cell_base {B W C F : Scheme.{u}}
    (w : W ⟶ B) (c0 : C ⟶ B) (f0 : F ⟶ B)
    (c : W ⟶ C) (j : W ⟶ F) (e : C ⟶ F)
    (he : e ≫ f0 = c0) (hj : j ≫ f0 = w) (h : c ≫ e = j) :
    c ≫ c0 = w := by
  calc
    c ≫ c0 = c ≫ (e ≫ f0) := congrArg (fun a => c ≫ a) he.symm
    _ = (c ≫ e) ≫ f0 := (Category.assoc _ _ _).symm
    _ = j ≫ f0 := congrArg (fun a => a ≫ f0) h
    _ = w := hj

private theorem conjugate_projection {A B C D E F : Scheme.{u}}
    (EC : A ≅ B) (EF : D ≅ E) (f : A ⟶ D) (e : C ⟶ F)
    (qC : A ⟶ C) (qF : D ⟶ F) (πC : B ⟶ C) (πF : E ⟶ F)
    (hC : EC.hom ≫ πC = qC) (hF : EF.hom ≫ πF = qF)
    (h : f ≫ qF = qC ≫ e) :
    (EC.inv ≫ f ≫ EF.hom) ≫ πF = πC ≫ e := by
  have hi : EC.inv ≫ qC = πC := by rw [← hC, Iso.inv_hom_id_assoc]
  calc
    (EC.inv ≫ f ≫ EF.hom) ≫ πF = EC.inv ≫ f ≫ qF := by
      simpa only [Category.assoc] using congrArg (fun a => EC.inv ≫ f ≫ a) hF
    _ = EC.inv ≫ (qC ≫ e) := congrArg (fun a => EC.inv ≫ a) h
    _ = πC ≫ e := (Category.assoc _ _ _).symm.trans
      (congrArg (fun a => a ≫ e) hi)

private theorem common_cell_stage {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) (C F : Over (Spec (.of S)))
    [QuasiSeparatedSpace C.left] [QuasiSeparatedSpace F.left]
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation F.hom]
    (e : C ⟶ F) (W CN FN : Over (Spec (.of K))) [IsAffine W.left]
    (c : W ⟶ CN) (j : W ⟶ FN)
    [IsOpenImmersion c.left] [IsOpenImmersion j.left]
    (eN : CN ⟶ FN) (hcell : c ≫ eN = j)
    (k : Spec (.of K) ⟶ W.left) (hk : k ≫ W.hom = 𝟙 _)
    (EC : CN ≅ genericScalarModel S C.hom)
    (EF : FN ≅ genericScalarModel S F.hom)
    (qC : CN.left ⟶ C.left) (qF : FN.left ⟶ F.left)
    (hEC : EC.hom.left ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) C.hom = qC)
    (hEF : EF.hom.left ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) F.hom = qF)
    (he : eN.left ≫ qF = qC ≫ e.left) (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t),
      ∀ (L : Type u) [Field L] [Algebra t.val L]
        (CL FL : Over (Spec (.of L)))
        [IrreducibleSpace CL.left] [IrreducibleSpace FL.left]
        (qCL : CL.left ⟶ C.left) (qFL : FL.left ⟶ F.left)
        (_hCL : IsPullback qCL CL.hom C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val L)) ≫
            Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)))
        (_hFL : IsPullback qFL FL.hom F.hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val L)) ≫
            Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)))
        (eL : CL ⟶ FL) (_heL : eL.left ≫ qFL = qCL ≫ e.left),
        Scheme.BirationalOver eL.left (𝟙 FL.left) := by
  let eK := EC.inv ≫ eN ≫ EF.hom
  let cK := c ≫ EC.hom
  let jK := j ≫ EF.hom
  let : IsOpenImmersion cK.left := by
    change IsOpenImmersion (c.left ≫ EC.hom.left)
    infer_instance
  let : IsOpenImmersion jK.left := by
    change IsOpenImmersion (j.left ≫ EF.hom.left)
    infer_instance
  have hcellK : cK ≫ eK = jK := by
    change (c ≫ EC.hom) ≫ (EC.inv ≫ eN ≫ EF.hom) = j ≫ EF.hom
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← hcell]
  have heK : eK.left ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) F.hom =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) C.hom ≫ e.left :=
    conjugate_projection ((Over.forget _).mapIso EC) ((Over.forget _).mapIso EF)
      eN.left e.left qC qF _ _ hEC hEF he
  obtain ⟨U, V, hU, hV, E, hE, s, hs, _⟩ :=
    exists_pointed_open_iso W _ _ cK jK eK hcellK k hk
  exact exists_birational_scalar_stage S hS C F e eK heK U hU V hV E hE s hs start

/-- For a reduced expression of the longest Weyl element, the prescribed word
and flag models have birational endpoints on all later irreducible field
fibres, after one coefficient extension preserving the original comparisons. -/
theorem exists_longest_birational_stage {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hw : simpleWeylWord G.rootBase word = G.longestElement)
    (S : Subalgebra ℤ K) (hS : S.FG) (C F : Over (Spec (.of S)))
    [QuasiSeparatedSpace C.left] [QuasiSeparatedSpace F.left]
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation F.hom]
    (e : C ⟶ F) (qC : bsdhScheme G word ⟶ C.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hC : IsPullback qC (bsdhToSpec G word) C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (he : qC ≫ e.left = bsdhMap G word ≫ qF) (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t),
      ∀ (L : Type u) [Field L] [Algebra t.val L]
        (CL FL : Over (Spec (.of L)))
        [IrreducibleSpace CL.left] [IrreducibleSpace FL.left]
        (qCL : CL.left ⟶ C.left) (qFL : FL.left ⟶ F.left)
        (_hCL : IsPullback qCL CL.hom C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val L)) ≫
            Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)))
        (_hFL : IsPullback qFL FL.hom F.hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val L)) ≫
            Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)))
        (eL : CL ⟶ FL) (_heL : eL.left ≫ qFL = qCL ≫ e.left),
        Scheme.BirationalOver eL.left (𝟙 FL.left) := by
  obtain ⟨c, hc, hj, hW, hcell, k, hk⟩ := exists_pointed_longest_cell G word hred hw
  let W := (schubertCell G (simpleWeylWord G.rootBase word)).toOver
  let CN : Over (Spec (.of K)) := Over.mk (bsdhToSpec G word)
  let FN := (flagVariety G).toOver
  let eN : CN ⟶ FN := Over.homMk (bsdhMap G word) rfl
  let j : W ⟶ FN := schubertCellInclusion G (simpleWeylWord G.rootBase word)
  let cN : W ⟶ CN := Over.homMk c
    (cell_base W.hom CN.hom FN.hom c j.left eN.left rfl j.w hcell)
  let : IsAffine W.left := hW
  let : IsOpenImmersion cN.left := hc
  let : IsOpenImmersion j.left := hj
  have hcellN : cN ≫ eN = j := CostructuredArrow.hom_ext _ _ hcell
  exact common_cell_stage S hS C F e W CN FN cN j eN hcellN k hk
    hC.flip.isoOverPullback hF.flip.isoOverPullback qC qF
    hC.flip.isoOverPullback_hom_left_comp_snd
    hF.flip.isoOverPullback_hom_left_comp_snd he.symm start

end SchubertGeometry
