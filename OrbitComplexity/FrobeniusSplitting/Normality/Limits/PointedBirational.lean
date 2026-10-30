import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Batteries.Tactic.Lint

/-! # Birationality from pointed common opens

A common open subscheme with a section remains nonempty after every base
change. If the two scalar fibres are irreducible, its open images are dense
and the endpoint is birational.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FrobeniusSplitting

universe u

private theorem common_open_birational {X Y W : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] [Nonempty W]
    (c : W ⟶ X) [IsOpenImmersion c] (j : W ⟶ Y) [IsOpenImmersion j]
    (f : X ⟶ Y) (h : c ≫ f = j) : Scheme.BirationalOver f (𝟙 Y) := by
  let U := c.opensRange
  let V := j.opensRange
  let E : W ≅ U.toScheme := IsOpenImmersion.isoOfRangeEq c U.ι
    (by simp only [Scheme.Opens.range_ι]; rfl)
  let F : W ≅ V.toScheme := IsOpenImmersion.isoOfRangeEq j V.ι
    (by simp only [Scheme.Opens.range_ι]; rfl)
  have hE : E.inv ≫ c = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  have hF : F.hom ≫ V.ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let P : Scheme.PartialIso X Y :=
    { source := U
      dense_source := IsOpenMap.denseRange_of_isPreirreducibleSpace c
        c.isOpenEmbedding.isOpenMap
      target := V
      dense_target := IsOpenMap.denseRange_of_isPreirreducibleSpace j
        j.isOpenEmbedding.isOpenMap
      iso := E.symm ≪≫ F }
  refine ⟨P, ?_⟩
  change (E.inv ≫ F.hom) ≫ V.ι ≫ 𝟙 Y = U.ι ≫ f
  calc
    (E.inv ≫ F.hom) ≫ V.ι ≫ 𝟙 Y = E.inv ≫ j := by
      simp only [Category.comp_id, Category.assoc, hF]
    _ = E.inv ≫ (c ≫ f) := congrArg (fun a => E.inv ≫ a) h.symm
    _ = U.ι ≫ f := (Category.assoc _ _ _).symm.trans
      (congrArg (fun a => a ≫ f) hE)

private theorem lifted_cell_open {B T : Scheme.{u}} (β : T ⟶ B)
    (W C : Over B) (c : W ⟶ C) [IsOpenImmersion c.left]
    (CT : Over T) (qC : CT.left ⟶ C.left)
    (hC : IsPullback qC CT.hom C.hom β) :
    IsOpenImmersion (hC.lift
      (pullback.snd β W.hom ≫ c.left) (pullback.fst β W.hom)
      (by rw [Category.assoc, c.w, pullback.condition])) := by
  have hW : IsPullback (pullback.snd β W.hom) (pullback.fst β W.hom)
      (c.left ≫ C.hom) β := by
    rw [c.w]
    exact (IsPullback.of_hasPullback β W.hom).flip
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (hW.of_bot' hC) inferInstance

/-- An endpoint with a pointed common open is birational on every pair of
irreducible scalar fibres in a Cartesian endpoint square. -/
theorem pointed_cell_birational {B T : Scheme.{u}} [Nonempty T]
    (W C F : Over B) (c : W ⟶ C) (j : W ⟶ F)
    [IsOpenImmersion c.left] [IsOpenImmersion j.left]
    (e : C ⟶ F) (h : c ≫ e = j)
    (k : B ⟶ W.left) (hk : k ≫ W.hom = 𝟙 B)
    (CT FT : Over T) [IrreducibleSpace CT.left] [IrreducibleSpace FT.left]
    (β : T ⟶ B) (qC : CT.left ⟶ C.left) (qF : FT.left ⟶ F.left)
    (hC : IsPullback qC CT.hom C.hom β)
    (hF : IsPullback qF FT.hom F.hom β)
    (eT : CT ⟶ FT) (he : eT.left ≫ qF = qC ≫ e.left) :
    Scheme.BirationalOver eT.left (𝟙 FT.left) := by
  let WT := pullback β W.hom
  let tW : WT ⟶ T := pullback.fst β W.hom
  let qW : WT ⟶ W.left := pullback.snd β W.hom
  let cT : WT ⟶ CT.left := hC.lift (qW ≫ c.left) tW
    (by rw [Category.assoc, c.w, pullback.condition])
  let jT : WT ⟶ FT.left := hF.lift (qW ≫ j.left) tW
    (by rw [Category.assoc, j.w, pullback.condition])
  let : IsOpenImmersion cT := lifted_cell_open β W C c CT qC hC
  let : IsOpenImmersion jT := lifted_cell_open β W F j FT qF hF
  have hcq : cT ≫ qC = qW ≫ c.left := hC.lift_fst _ _ _
  have hct : cT ≫ CT.hom = tW := hC.lift_snd _ _ _
  have hjq : jT ≫ qF = qW ≫ j.left := hF.lift_fst _ _ _
  have hjt : jT ≫ FT.hom = tW := hF.lift_snd _ _ _
  have hleft : c.left ≫ e.left = j.left :=
    congrArg (fun a : W ⟶ F => a.left) h
  have hT : cT ≫ eT.left = jT := by
    apply hF.hom_ext
    · calc
        (cT ≫ eT.left) ≫ qF = cT ≫ (eT.left ≫ qF) := Category.assoc _ _ _
        _ = cT ≫ (qC ≫ e.left) := congrArg (fun a => cT ≫ a) he
        _ = (cT ≫ qC) ≫ e.left := (Category.assoc _ _ _).symm
        _ = (qW ≫ c.left) ≫ e.left := congrArg (fun a => a ≫ e.left) hcq
        _ = qW ≫ j.left := (Category.assoc _ _ _).trans
          (congrArg (fun a => qW ≫ a) hleft)
        _ = jT ≫ qF := hjq.symm
    · calc
        (cT ≫ eT.left) ≫ FT.hom = cT ≫ (eT.left ≫ FT.hom) := Category.assoc _ _ _
        _ = cT ≫ CT.hom := congrArg (fun a => cT ≫ a) eT.w
        _ = tW := hct
        _ = jT ≫ FT.hom := hjt.symm
  let s : T ⟶ WT := pullback.lift (𝟙 T) (β ≫ k)
    (by simp only [Category.id_comp, Category.assoc, hk, Category.comp_id])
  let : Nonempty WT := Nonempty.map s inferInstance
  exact common_open_birational cT jT eT.left hT

end FrobeniusSplitting
