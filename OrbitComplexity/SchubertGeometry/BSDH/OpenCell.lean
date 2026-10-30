import OrbitComplexity.SchubertGeometry.BSDH.EndpointCharts
import OrbitComplexity.SchubertGeometry.BSDH.Variety
import OrbitComplexity.SchubertGeometry.Deodhar.ProductAction
import OrbitComplexity.SchubertGeometry.Deodhar.InitialCell
import OrbitComplexity.SchubertGeometry.Cells.Longest
import OrbitComplexity.SchubertGeometry.ProjectiveLine.Charts
import OrbitComplexity.GroupActions.Varieties.ProductImmersions
import Mathlib.AlgebraicGeometry.Birational.Birational
import OrbitComplexity.SchubertGeometry.Deodhar.PrefixCharts

/-! # Open Schubert cells in reduced BSDH schemes -/

noncomputable section
namespace SchubertGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def cellOpposite (w : G.weylGroup) : (schubertCell G w).toOver ⟶
    (oppositeUnipotentVariety G).toOver :=
  (schubertCellIso G w).inv ≫ schubertOppositeMorphism G w

private theorem cellOpposite_chart (w : G.weylGroup) :
    cellOpposite G w ≫ flagChartMorphism G (G.weylPoint w) =
      schubertCellInclusion G w := by
  rw [cellOpposite, Category.assoc, schubertRootMorphism_chart,
    ← schubertCellIso_hom_comp, Iso.inv_hom_id_assoc]

private theorem cellOpposite_lift (w : G.weylGroup) :
    cellOpposite G w ≫ flagChartMap G (G.weylPoint w) = schubertCellLift G w := by
  apply Variety.mapPoints_injective
  funext z
  rw [Variety.mapPoints_comp, flagChartMap_points, schubertCellLift_points]
  change reductivePointsEquiv G
    (G.weylPoint w * (oppositeUnipotentPointsMulEquiv G
      (Variety.mapPoints (schubertOppositeMorphism G w)
        (Variety.mapPoints (schubertCellIso G w).inv z)) : G.points)) = _
  rw [schubertOppositeMorphism_points]
  congr 1
  group

private theorem initial_cell_endpoint :
    (initialCellIso G).hom.left ≫ (schubertCellInclusion G 1).left =
      (baseFlagPoint G).val := by
  let p : (affineVariety K K).points := affinePointsEquiv (AlgHom.id K K)
  have hp : p.val = 𝟙 (Spec (.of K)) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id K)) = _
    exact Spec.map_id _
  have h := congrArg Subtype.val (initialCellIso_points G p)
  change p.val ≫ ((initialCellIso G).hom.left ≫ (schubertCellInclusion G 1).left) =
    (baseFlagPoint G).val at h
  rw [hp] at h
  exact (Category.id_comp _).symm.trans h

private theorem initial_cell_open :
    ∃ c : (schubertCell G 1).scheme ⟶ bsdhScheme G [],
      IsOpenImmersion c ∧ c ≫ bsdhMap G [] = (schubertCellInclusion G 1).left := by
  let e := (Over.forget (Spec (.of K))).mapIso (initialCellIso G)
  have : IsIso e.inv := inferInstance
  refine ⟨e.inv, IsOpenImmersion.of_isIso e.inv, ?_⟩
  change e.inv ≫ (baseFlagPoint G).val = (schubertCellInclusion G 1).left
  rw [← initial_cell_endpoint G]
  exact e.inv_hom_id_assoc _

private theorem chart_endpoint (word : List G.rootBase.support) (i : G.rootBase.support)
    (U : Over (Spec (.of K))) (a : U ⟶ (oppositeUnipotentVariety G).toOver) (g : G.points)
    (k : U ⊗ (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
      Over.mk (bsdhToSpec G (word ++ [i])))
    (hk : k.left ≫ (bsdhAppendIso G word i).hom.left ≫
        pullback.snd (bsdhMap G word) (flagBundleProjection G
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫ flagBundleChart G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) g) :
    k.left ≫ bsdhMap G (word ++ [i]) =
      (a ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
        ((fst (oppositeUnipotentVariety G).toOver
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ≫
            flagChartMap G g) •
          (snd (oppositeUnipotentVariety G).toOver
            (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ≫
              schubertInclusion G
            (RootPairing.weylGroup.ofIdx G.rootSystem i.val))).left := by
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let j := schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  calc
    _ = k.left ≫ (bsdhAppendIso G word i).hom.left ≫
        pullback.snd (bsdhMap G word) (flagBundleProjection G Y) ≫
          flagBundleMap G Y j := by
            simpa only [Category.assoc] using
              congrArg (fun f ↦ k.left ≫ f) (bsdhAppendIso_endpoint G word i).symm
    _ = ((a ⊗ₘ 𝟙 Y.toOver).left ≫ flagBundleChart G Y g) ≫
        flagBundleMap G Y j := by
          simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ flagBundleMap G Y j) hk
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ (a ⊗ₘ 𝟙 Y.toOver).left ≫ f) (flagBundleChart_map G Y j g)

private theorem cell_product_action (w : G.weylGroup) (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val)) :
    (𝟙 (schubertCell G w).toOver ⊗ₘ simplePositiveChart G i) ≫
        (cellOpposite G w ⊗ₘ 𝟙 (schubertVariety G
          (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫
          ((fst (oppositeUnipotentVariety G).toOver
            (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ≫
              flagChartMap G (G.weylPoint w)) •
            (snd (oppositeUnipotentVariety G).toOver
              (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ≫
                schubertInclusion G
              (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (rankOneCellProductIso G w i hi).hom ≫
        schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  rw [rankOneCellProductIso_action]
  simp only [ModObj.comp_smul, tensorHom_fst_assoc, tensorHom_snd_assoc,
    Category.id_comp, cellOpposite_lift, simplePositiveChart,
    Category.assoc, schubertCellOfLE_comp]

private theorem cell_bundle_chart (word : List G.rootBase.support) (w : G.weylGroup)
    (i : G.rootBase.support) (c : (schubertCell G w).scheme ⟶ bsdhScheme G word)
    [IsOpenImmersion c]
    (hc : c ≫ bsdhMap G word = (schubertCellInclusion G w).left) :
    ∃ k : (schubertCell G w).toOver ⊗
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
          Over.mk (bsdhToSpec G (word ++ [i])),
      IsOpenImmersion k.left ∧
        k.left ≫ bsdhMap G (word ++ [i]) =
          (cellOpposite G w ⊗ₘ 𝟙 (schubertVariety G
            (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          ((fst (oppositeUnipotentVariety G).toOver
            (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ≫
              flagChartMap G (G.weylPoint w)) •
            (snd (oppositeUnipotentVariety G).toOver
              (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ≫
                schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))).left := by
  let C := (schubertCell G w).toOver
  let b : C ⟶ Over.mk (bsdhToSpec G word) := Over.homMk c (by
    change c ≫ bsdhMap G word ≫ (flagVariety G).toSpec = _
    rw [← Category.assoc, hc]
    exact (schubertCellInclusion G w).w)
  have : IsOpenImmersion b.left := show IsOpenImmersion c from inferInstance
  let a := cellOpposite G w
  have hchart : a.left ≫ flagSchemeChart G (G.weylPoint w) = c ≫ bsdhMap G word :=
    (congrArg Over.Hom.left (cellOpposite_chart G w)).trans hc.symm
  obtain ⟨k, _, hkopen, hk⟩ := bsdh_append_chart_endpoint G word i C b
    (G.weylPoint w) a hchart
  exact ⟨k, hkopen, chart_endpoint G word i C a (G.weylPoint w) k hk⟩

private theorem restricted_cell_endpoint (word : List G.rootBase.support) (w : G.weylGroup)
    (i : G.rootBase.support) (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val))
    (k : (schubertCell G w).toOver ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hk : k.left ≫ bsdhMap G (word ++ [i]) =
      (cellOpposite G w ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
        ((fst (oppositeUnipotentVariety G).toOver
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ≫
            flagChartMap G (G.weylPoint w)) •
          (snd (oppositeUnipotentVariety G).toOver
            (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ≫
              schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))).left) :
    (𝟙 (schubertCell G w).toOver ⊗ₘ simplePositiveChart G i).left ≫
        k.left ≫ bsdhMap G (word ++ [i]) =
      (rankOneCellProductIso G w i hi).hom.left ≫
        (schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left := by
  rw [hk]
  exact congrArg Over.Hom.left (cell_product_action G w i hi)

omit [IsAlgClosed K] [CharZero K] in
private theorem open_transport {A B C D T : Scheme.{u}} (e : A ≅ B)
    (v : A ⟶ C) [IsOpenImmersion v] (k : C ⟶ D) [IsOpenImmersion k]
    (f : D ⟶ T) (j : B ⟶ T) (h : v ≫ k ≫ f = e.hom ≫ j) :
    ∃ d : B ⟶ D, IsOpenImmersion d ∧ d ≫ f = j := by
  have : IsOpenImmersion e.inv := IsOpenImmersion.of_isIso e.inv
  refine ⟨e.inv ≫ v ≫ k, inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, h, e.inv_hom_id_assoc]

private theorem append_cell_open (word : List G.rootBase.support) (w : G.weylGroup)
    (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val))
    (c : (schubertCell G w).scheme ⟶ bsdhScheme G word) [IsOpenImmersion c]
    (hc : c ≫ bsdhMap G word = (schubertCellInclusion G w).left) :
    ∃ d : (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).scheme
        ⟶ bsdhScheme G (word ++ [i]),
      IsOpenImmersion d ∧ d ≫ bsdhMap G (word ++ [i]) =
        (schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left := by
  obtain ⟨k, hkopen, hkend⟩ := cell_bundle_chart G word w i c hc
  let C := (schubertCell G w).toOver
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let v : C ⊗ (additiveVariety K).toOver ⟶ C ⊗ Y.toOver :=
    𝟙 C ⊗ₘ simplePositiveChart G i
  have : IsOpenImmersion (𝟙 C : C ⟶ C).left := by
    change IsOpenImmersion (𝟙 C.left)
    exact IsOpenImmersion.of_isIso _
  have : IsOpenImmersion v.left := tensorHom_isOpen (𝟙 C) (simplePositiveChart G i)
  have : IsOpenImmersion k.left := hkopen
  exact open_transport ((Over.forget (Spec (.of K))).mapIso
    (rankOneCellProductIso G w i hi)) v.left k.left (bsdhMap G (word ++ [i]))
      (schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left
      (restricted_cell_endpoint G word w i hi k hkend)

/-- A reduced-word Schubert cell embeds openly in its BSDH scheme with its flag endpoint. -/
theorem bsdh_cell_open (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    ∃ c : (schubertCell G (simpleWeylWord G.rootBase word)).scheme ⟶ bsdhScheme G word,
      IsOpenImmersion c ∧
        c ≫ bsdhMap G word = (schubertCellInclusion G (simpleWeylWord G.rootBase word)).left := by
  induction word using List.reverseRecOn with
  | nil => exact initial_cell_open G
  | append_singleton word i ih =>
    have hprefix : (weylCoxeterSystem G.rootBase).IsReduced word := by
      simpa using hred.take word.length
    have hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
        (simpleWeylWord G.rootBase word) i.val) := by
      simpa using wordCell_ascent G (word ++ [i]) hred word.length (by simp)
    obtain ⟨c, hc, hfac⟩ := ih hprefix
    let : IsOpenImmersion c := hc
    rw [simpleWeylWord_append_singleton]
    exact append_cell_open G word (simpleWeylWord G.rootBase word) i hi c hfac

end SchubertGeometry
