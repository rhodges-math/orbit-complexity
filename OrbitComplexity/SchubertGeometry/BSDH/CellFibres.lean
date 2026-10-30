import OrbitComplexity.SchubertGeometry.BSDH.Actions
import OrbitComplexity.SchubertGeometry.Cells.BorelSection
import OrbitComplexity.GroupActions.Actions.OrbitSection
import OrbitComplexity.GroupActions.Varieties.GeometricConnected
import OrbitComplexity.SchubertGeometry.BSDH.Factorization
import OrbitComplexity.SchubertGeometry.Levi.Schubert
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-! # Cell fibres of iterated endpoints

A regular Borel-valued cell section identifies an endpoint pullback with a product.
Connectedness of its Weyl fibre therefore gives geometric connectedness over the cell.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
universe u

private instance connected_respectsIso : MorphismProperty.RespectsIso @GeometricallyConnected :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private abbrev flagMorphism (word : List G.rootBase.support) :
    (bsdhVariety G word).toOver ⟶ (flagVariety G).toOver :=
  Over.homMk (bsdhMap G word) rfl

private theorem section_condition (w : G.weylGroup) :
    schubertCellInclusion G w = lift (schubertCellBorelSection G w)
      (toUnit (schubertCell G w).toOver ≫
        (flagVariety G).pointsEquivOverHom (weylFlagPoint G w)) ≫
          γ[(borelVariety G).toOver, (flagVariety G).toOver] := by
  rw [← schubertCellBorelSection_orbit G w]
  simp only [Variety.orbitMorphism, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]

/-- The cell pullback of an iterated endpoint is its product with the Weyl fibre. -/
theorem bsdhCellTrivialization (word : List G.rootBase.support) (w : G.weylGroup) :
    letI := bsdhBorelAction G word
    let f := flagMorphism G word
    let y := (flagVariety G).pointsEquivOverHom (weylFlagPoint G w)
    let c := schubertCellInclusion G w
    let s := schubertCellBorelSection G w
    let F := pullback f y
    ∃ e : pullback f c ≅ (schubertCell G w).toOver ⊗ F,
      (e.hom ≫ fst (schubertCell G w).toOver F = pullback.snd f c) ∧
      (e.inv ≫ pullback.snd f c = fst (schubertCell G w).toOver F) ∧
      (e.inv ≫ pullback.fst f c =
        lift (fst (schubertCell G w).toOver F ≫ s)
          (snd (schubertCell G w).toOver F ≫ pullback.fst f y) ≫
            γ[(borelVariety G).toOver, (bsdhVariety G word).toOver]) ∧
      (e.hom ≫ snd (schubertCell G w).toOver F ≫ pullback.fst f y =
        lift ((pullback.snd f c ≫ s)⁻¹) (pullback.fst f c) ≫
          γ[(borelVariety G).toOver, (bsdhVariety G word).toOver]) := by
  let := bsdhBorelAction G word
  let f := flagMorphism G word
  let y := (flagVariety G).pointsEquivOverHom (weylFlagPoint G w)
  let c := schubertCellInclusion G w
  let s := schubertCellBorelSection G w
  let : IsModHom (borelVariety G).toOver f := bsdhBorelEquivariant G word
  have hc : c = lift s (toUnit (schubertCell G w).toOver ≫ y) ≫
      γ[(borelVariety G).toOver, (flagVariety G).toOver] := section_condition G w
  refine ⟨orbitSectionIso f y c s hc, ?_, ?_, ?_, ?_⟩
  · exact orbitSectionIso_hom_fst f y c s hc
  · exact orbitSectionIso_inv_snd f y c s hc
  · exact orbitSectionIso_inv_fst f y c s hc
  · exact orbitSectionIso_hom_snd_fst f y c s hc

section PullbackComparison
variable {C : Type*} [Category C] {X Z Y A : C}
  (f : X ⟶ Z) (j : Z ⟶ Y) [Mono j] (c : A ⟶ Z)
  [HasPullback f c] [HasPullback (f ≫ j) (c ≫ j)]

private def factorPullbackIso : pullback f c ≅ pullback (f ≫ j) (c ≫ j) :=
  (limit.isoLimitCone ⟨_, pullbackIsPullbackOfCompMono f c j⟩).symm

private theorem factorPullbackIso_snd :
    (factorPullbackIso f j c).hom ≫ pullback.snd (f ≫ j) (c ≫ j) = pullback.snd f c :=
  limit.isoLimitCone_inv_π ⟨_, pullbackIsPullbackOfCompMono f c j⟩ WalkingCospan.right

end PullbackComparison

private theorem rawCell_geometricallyConnected (word : List G.rootBase.support)
    (x : G.weylGroup)
    (hconn : ConnectedSpace (pullback (bsdhMap G word) (weylFlagPoint G x).val : Scheme)) :
    GeometricallyConnected
      (pullback.snd (bsdhMap G word) (schubertCellInclusion G x).left) := by
  let f : (bsdhVariety G word).toOver ⟶ (flagVariety G).toOver :=
    Over.homMk (bsdhMap G word) rfl
  let y := (flagVariety G).pointsEquivOverHom (weylFlagPoint G x)
  let c := schubertCellInclusion G x
  let F := pullback f y
  let q := PreservesPullback.iso (Over.forget (Spec (CommRingCat.of K))) f y
  have hc : ConnectedSpace (pullback f.left y.left : Scheme) := hconn
  let : ConnectedSpace F.left := q.hom.homeomorph.connectedSpace_iff.mpr hc
  let : GeometricallyConnected F.hom := geometricallyConnected_of_algClosed F.hom
  obtain ⟨e, he, _, _, _⟩ := bsdhCellTrivialization G word x
  have he' : e.hom.left ≫ (fst (schubertCell G x).toOver F).left =
      (pullback.snd f c).left := congrArg (fun a => a.left) he
  have hp : GeometricallyConnected (fst (schubertCell G x).toOver F).left := by
    change GeometricallyConnected (pullback.fst (schubertCell G x).toOver.hom F.hom)
    infer_instance
  have hec : GeometricallyConnected (pullback.snd f c).left := by
    rw [← he']
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected
      e.hom.left _).mpr hp
  let r := PreservesPullback.iso (Over.forget (Spec (CommRingCat.of K))) f c
  have hr : r.hom ≫ pullback.snd f.left c.left = (pullback.snd f c).left :=
    PreservesPullback.iso_hom_snd (Over.forget (Spec (CommRingCat.of K))) f c
  change GeometricallyConnected (pullback.snd f.left c.left)
  apply (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected r.hom _).mp
  rw [hr]
  exact hec

/-- A connected Weyl fibre gives connected geometric fibres over its Schubert cell. -/
theorem bsdhCell_geomConnected (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) (x : G.weylGroup)
    (hx : WeylBruhatLE G.rootBase x (simpleWeylWord G.rootBase word))
    (hconn : ConnectedSpace (pullback (bsdhMap G word) (weylFlagPoint G x).val : Scheme)) :
    GeometricallyConnected (pullback.snd (bsdhSchubertMap G word hred).left
      (schubertCellOfLE G x (simpleWeylWord G.rootBase word) hx).left) := by
  let f := (bsdhSchubertMap G word hred).left
  let j := (schubertInclusion G (simpleWeylWord G.rootBase word)).left
  let c := (schubertCellOfLE G x (simpleWeylWord G.rootBase word) hx).left
  have hf : f ≫ j = bsdhMap G word := bsdhSchubertMap_comp G word hred
  have hc : c ≫ j = (schubertCellInclusion G x).left :=
    congrArg (fun a => a.left) (schubertCellOfLE_comp G x
      (simpleWeylWord G.rootBase word) hx)
  let e := factorPullbackIso f j c ≪≫ pullback.congrHom hf hc
  have hcongr : (pullback.congrHom hf hc).hom ≫
      pullback.snd (bsdhMap G word) (schubertCellInclusion G x).left =
        pullback.snd (f ≫ j) (c ≫ j) := by
    simp only [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  have he : e.hom ≫ pullback.snd (bsdhMap G word) (schubertCellInclusion G x).left =
      pullback.snd f c := by
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, hcongr]
    exact factorPullbackIso_snd f j c
  change GeometricallyConnected (pullback.snd f c)
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected e.hom _).mpr
    (rawCell_geometricallyConnected G word x hconn)

end SchubertGeometry
