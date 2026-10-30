import OrbitComplexity.SchubertGeometry.BSDH.Points
import OrbitComplexity.GroupActions.Actions.ProductChartPoints
import OrbitComplexity.SchubertGeometry.Levi.Schubert
import OrbitComplexity.SchubertGeometry.Deodhar.ProductAction
import OrbitComplexity.SchubertGeometry.Deodhar.PrefixCharts
import OrbitComplexity.SchubertGeometry.Cells.SchubertPoints
/-! # Reduced-cell points in BSDH endpoint images

The increasing cell product lifts through the append pullback. Induction on a reduced
word then lifts every rational point in the corresponding Schubert cell.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem cell_one_point (z : (schubertCell G 1).points) :
    GroupActions.Variety.mapPoints (schubertCellInclusion G 1) z = baseFlagPoint G := by
  have hw : weylFlagPoint G 1 = baseFlagPoint G := by
    unfold weylFlagPoint baseFlagPoint baseFlag
    rw [G.weylPoint_eq, ReductiveGroups.weylElementPoint_one]
  have hz : GroupActions.Variety.mapPoints (schubertCellInclusion G 1) z ∈
      MulAction.orbit (GroupActions.borelVariety G).points (weylFlagPoint G 1) := by
    rw [← schubertCell_points_range]
    exact ⟨z, rfl⟩
  obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hz
  rw [hw] at hb
  apply hb.symm.trans
  rw [baseFlagPoint, borelFlag_smul]
  apply congrArg (flagVarietyPointsEquiv G)
  have hb' : (GroupActions.borelPointsMulEquiv G b : G.points) ∈
      MulAction.stabilizer G.points (baseFlag G) := by
    rw [baseFlagStabilizer]
    exact (GroupActions.borelPointsMulEquiv G b).property
  exact hb'

omit [IsAlgClosed K] [CharZero K] in
private theorem pointMulEquiv_apply (g : G.points) :
    GroupActions.reductivePointsMulEquiv G g = GroupActions.reductivePointsEquiv G g := rfl

attribute [local irreducible] GroupActions.reductivePointsMulEquiv
  GroupActions.reductivePointsEquiv schubertCellLift rankOneCellProductIso

private theorem bsdhCell_append (word : List G.rootBase.support) (w : G.weylGroup)
    (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val))
    (hpoints : ∀ x : (schubertCell G w).points,
      ∃ q : Spec (CommRingCat.of K) ⟶ bsdhScheme G word,
        q ≫ bsdhMap G word =
          (GroupActions.Variety.mapPoints (schubertCellInclusion G w) x).val)
    (z : (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).points) :
    ∃ p : Spec (CommRingCat.of K) ⟶ bsdhScheme G (word ++ [i]),
      p ≫ bsdhMap G (word ++ [i]) =
        (GroupActions.Variety.mapPoints (schubertCellInclusion G
          (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) z).val := by
  obtain ⟨x, a, hxa⟩ := GroupActions.Variety.exists_productChart_points
    (schubertCell G (w))
    (GroupActions.additiveVariety K)
    (schubertCell G (w *
      RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (GroupActions.reductiveVariety G) (flagVariety G)
    (rankOneCellProductIso G (w) i hi)
    (schubertCellLift G (w))
    ((simpleCellIso G i).hom ≫ schubertCellInclusion G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (schubertCellInclusion G (w *
      RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (rankOneCellProductIso_action G
      (w) i hi) z
  obtain ⟨q, hq⟩ := hpoints x
  let g := (GroupActions.reductivePointsEquiv G).symm
    (GroupActions.Variety.mapPoints (schubertCellLift G w) x)
  have hgp : GroupActions.reductivePointsEquiv G g =
      GroupActions.Variety.mapPoints (schubertCellLift G w) x :=
    (GroupActions.reductivePointsEquiv G).apply_symm_apply _
  have hsq : GroupActions.Variety.mapPoints (schubertCellInclusion G w) x =
      GroupActions.Variety.mapPoints (flagQuotientMorphism G)
        (GroupActions.Variety.mapPoints (schubertCellLift G w) x) :=
    (congrArg (fun f => GroupActions.Variety.mapPoints f x)
      (schubertCellLift_quotient G w)).symm.trans
        (GroupActions.Variety.mapPoints_comp (schubertCellLift G w)
          (flagQuotientMorphism G) x)
  have hgflag : GroupActions.Variety.mapPoints (schubertCellInclusion G w) x =
      flagVarietyPointsEquiv G (flagProjection G g) :=
    hsq.trans ((congrArg (GroupActions.Variety.mapPoints (flagQuotientMorphism G))
      hgp.symm).trans (flagQuotientMorphism_points G g))
  let si := RootPairing.weylGroup.ofIdx G.rootSystem i.val
  let y := GroupActions.Variety.mapPoints ((simpleCellIso G i).hom ≫
    schubertCellOfLE G si si (ReductiveGroups.WeylBruhatLE.refl G.rootBase si)) a
  have hy : GroupActions.Variety.mapPoints (schubertInclusion G si) y =
      GroupActions.Variety.mapPoints ((simpleCellIso G i).hom ≫
        schubertCellInclusion G si) a := by
    dsimp only [y]
    rw [← GroupActions.Variety.mapPoints_comp, Category.assoc, schubertCellOfLE_comp]
  have hqg : q ≫ bsdhMap G word =
      (flagVarietyPointsEquiv G (flagProjection G g)).val :=
    hq.trans (congrArg Subtype.val hgflag)
  refine ⟨bsdhAppendPoint G word i q g hqg y, ?_⟩
  have hgm : GroupActions.reductivePointsMulEquiv G g =
      GroupActions.Variety.mapPoints (schubertCellLift G w) x :=
    (pointMulEquiv_apply G g).trans hgp
  have ha : GroupActions.reductivePointsMulEquiv G g •
      GroupActions.Variety.mapPoints (schubertInclusion G si) y =
        GroupActions.Variety.mapPoints (schubertCellInclusion G
          (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) z :=
    (congrArg₂ (fun (h : (GroupActions.reductiveVariety G).points)
      (p : (flagVariety G).points) => h • p) hgm hy).trans hxa.symm
  exact (bsdhAppendPoint_endpoint G word i q g hqg y).trans (congrArg Subtype.val ha)


/-- Every rational point of a reduced-word Schubert cell lifts through the BSDH endpoint. -/
theorem bsdhMap_cell_range (word : List G.rootBase.support)
    (hred : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced word) :
    Set.range (GroupActions.Variety.mapPoints (schubertCellInclusion G
      (ReductiveGroups.simpleWeylWord G.rootBase word))) ⊆
        {z | ∃ p : Spec (CommRingCat.of K) ⟶ bsdhScheme G word,
          p ≫ bsdhMap G word = z.val} := by
  induction word using List.reverseRecOn with
  | nil =>
    change Set.range (GroupActions.Variety.mapPoints (schubertCellInclusion G 1)) ⊆ _
    rintro _ ⟨z, rfl⟩
    refine ⟨𝟙 _, ?_⟩
    exact (Category.id_comp _).trans (congrArg Subtype.val (cell_one_point G z)).symm
  | append_singleton word i ih =>
    have hprefix : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced word := by
      simpa using hred.take word.length
    have hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
        (ReductiveGroups.simpleWeylWord G.rootBase word) i.val) := by
      simpa using wordCell_ascent G (word ++ [i]) hred word.length (by simp)
    rw [ReductiveGroups.simpleWeylWord_append_singleton]
    rintro _ ⟨z, rfl⟩
    exact bsdhCell_append G word (ReductiveGroups.simpleWeylWord G.rootBase word) i hi
      (fun x => ih hprefix ⟨x, rfl⟩) z

end SchubertGeometry
